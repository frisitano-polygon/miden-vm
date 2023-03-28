use super::build_test;
use miden::{crypto::Rpo256, math::Felt};
use vm_core::{
    crypto::merkle::{EmptySubtreeRoots, MerkleStore, NodeIndex},
    utils::IntoBytes,
    StarkField, Word, WORD_SIZE, ZERO,
};

#[test]
fn smtget_opens_correctly() {
    let empty = EmptySubtreeRoots::empty_hashes(64);
    let initial_root = Word::from(empty[0]);
    let seed = blake3::hash(b"some-seed");

    // compute pseudo-random key/value pair
    let key = <[u8; 8]>::try_from(&seed.as_bytes()[..8]).unwrap();
    let key = u64::from_le_bytes(key);
    let key = Felt::new(key);
    let key = [key, key + Felt::new(1), key + Felt::new(2), key + Felt::new(3)];
    let value = <[u8; 8]>::try_from(&seed.as_bytes()[8..16]).unwrap();
    let value = u64::from_le_bytes(value);
    let value = Felt::new(value);
    let value = [value, value + Felt::new(1), value + Felt::new(2), value + Felt::new(3)];

    fn assert_case(
        key: Word,
        value: Word,
        root: Word,
        store: MerkleStore,
        advice_map: &[([u8; 32], Vec<Felt>)],
    ) {
        let source = r#"
            use.std::collections::smt

            begin
                exec.smt::get
            end
        "#;
        let initial_stack = [
            root[0].as_int(),
            root[1].as_int(),
            root[2].as_int(),
            root[3].as_int(),
            key[0].as_int(),
            key[1].as_int(),
            key[2].as_int(),
            key[3].as_int(),
        ];
        let expected_output = [
            value[3].as_int(),
            value[2].as_int(),
            value[1].as_int(),
            value[0].as_int(),
            root[3].as_int(),
            root[2].as_int(),
            root[1].as_int(),
            root[0].as_int(),
        ];
        let advice_stack = [];
        build_test!(source, &initial_stack, &advice_stack, store, advice_map.iter().cloned())
            .expect_stack(&expected_output);
    }

    // check empty tree
    let store = MerkleStore::new();
    let advice_map = [];
    let expected = [ZERO; WORD_SIZE];
    assert_case(key, expected, initial_root, store, &advice_map);

    // check included leaves for all tiers
    for depth in [16, 32, 48, 64] {
        // compute the index and node value
        let index = key[3].as_int();
        let index = index >> (64 - depth);
        let index = NodeIndex::new(depth as u8, index);
        let mut remaining = key;
        remaining[3] = Felt::new((remaining[3].as_int() << depth.min(63)) >> depth.min(63));
        let node =
            Rpo256::merge_in_domain(&[remaining.into(), value.into()], Felt::new(depth)).into();

        // setup the store and run the test
        let mut store = MerkleStore::new();
        let root = store.set_node(initial_root, index, node).unwrap().root;
        let advice_map = [(node.into_bytes(), value.to_vec())];
        assert_case(key, value, root, store, &advice_map);
    }

    // check non-included leaf with same path sibling, except for last bit
    {
        // compute a sibling index and node value
        let mut sibling = key[3].as_int();
        sibling ^= 1;
        let mut remaining = key;
        remaining[3] = ZERO;
        let sibling = NodeIndex::new(64, sibling);
        let node = Rpo256::merge_in_domain(&[remaining.into(), value.into()], Felt::new(64)).into();

        // setup the store and run the test; expect ZERO as the leaf isn't included
        let mut store = MerkleStore::new();
        let root = store.set_node(initial_root, sibling, node).unwrap().root;
        let advice_map = [(node.into_bytes(), value.to_vec())];
        let expected = [ZERO; WORD_SIZE];
        assert_case(key, expected, root, store, &advice_map);
    }
}

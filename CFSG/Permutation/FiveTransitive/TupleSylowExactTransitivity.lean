module

public import CFSG.Permutation.FiveTransitive.ExactFixedSetTransitivity
public import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy
public import CFSG.Permutation.FiveTransitive.OyamaMinimalOrbitDescent

public section

namespace CFSG

namespace FiveTransitive.TupleSylowExactTransitivity

open MulAction OyamaMinimalOrbitDescent

private theorem range_subset_fixed
    {G X : Type*} [Group G] [MulAction G X] {k : ℕ} (a : Fin k ↪ X)
    (S : Sylow 2 (stabilizer G a)) :
    Set.range a ⊆ fixedPoints (ambientSylow a S) X := by
  rintro _ ⟨i, rfl⟩
  intro q
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp q.property
  have hf : u.val • a i = a i := DFunLike.congr_fun u.property i
  change q.val • a i = a i
  rw [← he]
  exact hf

theorem multiply_of_tuple_sylow_fixed_card
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (k : ℕ) (hsize : k + 1 ≤ Nat.card X)
    (hlocal : ∀ a : Fin k ↪ X, ∃ S : Sylow 2 (stabilizer G a),
      Nat.card (fixedPoints (ambientSylow a S) X) = k) :
    IsMultiplyPretransitive G X k := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  apply ExactFixedSetTransitivity.multiply_of_exact_two_subgroup_fixed_sets k hsize
  intro s hs
  obtain ⟨a, ha⟩ := BaseSylowConjugacy.exists_embedding_range X k s hs
  obtain ⟨S, hS⟩ := hlocal a
  refine ⟨ambientSylow a S, S.isPGroup'.map (stabilizer G a).subtype, ?_⟩
  have hsub : s ⊆ fixedPoints (ambientSylow a S) X := by
    rw [← ha]
    exact range_subset_fixed a S
  apply (Set.eq_of_subset_of_ncard_le hsub ?_).symm
  rw [← Nat.card_coe_set_eq, hS, hs]

end FiveTransitive.TupleSylowExactTransitivity

end CFSG

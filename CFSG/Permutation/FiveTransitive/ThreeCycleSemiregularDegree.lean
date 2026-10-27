module

public import CFSG.Permutation.FiveTransitive.SmallSupportSeven
public import CFSG.Permutation.FiveTransitive.PrimeTupleSemiregularFixed
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

namespace CFSG

namespace FiveTransitive.ThreeCycleSemiregularDegree

private theorem exists_even_three_cycle
    (X : Type) [Fintype X] [DecidableEq X] (hcard : 3 ≤ Fintype.card X) :
    ∃ g : Equiv.Perm X, g ∈ alternatingGroup X ∧ orderOf g = 3 ∧
      g.support.card = 3 ∧
      Fintype.card (Function.fixedPoints g) = Fintype.card X - 3 := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin 3 ↪ X) := Function.Embedding.nonempty_of_card_le (by simpa using hcard)
  let c : Equiv.Perm (Fin 3) := List.formPerm [0,1,2]
  let f := Equiv.Perm.viaEmbeddingHom e
  let g := f c
  have hf : Function.Injective f := by
    intro a b h
    apply Equiv.ext
    intro x
    have hh := congrArg (fun t : Equiv.Perm X => t (e x)) h
    exact e.injective (by simpa only [f,Equiv.Perm.viaEmbeddingHom_apply,Equiv.Perm.viaEmbedding_apply] using hh)
  have hc : orderOf c = 3 := by
    have hcyc : c.IsCycle := List.isCycle_formPerm (by decide) (by norm_num)
    rw [hcyc.orderOf]
    decide
  have hg : orderOf g = 3 := (orderOf_injective f hf c).trans hc
  have hsign3 : g.sign ^ 3 = 1 := by rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
  have hsign : g.sign = 1 := by
    rcases Int.units_eq_one_or g.sign with h | h
    · exact h
    · rw [h] at hsign3
      norm_num at hsign3
  have hs : g.support.card = 3 := by
    change (c.viaEmbedding e).support.card = 3
    rw [SmallSupportSeven.support_card_viaEmbedding]
    decide
  refine ⟨g,Equiv.Perm.mem_alternatingGroup.mpr hsign,hg,hs,?_⟩
  rw [Equiv.Perm.card_fixedPoints,g.sum_cycleType,hs]

open MulAction TupleSemiregularFour

theorem card_le_fixed_add_three
    (X : Type) [Fintype X] [DecidableEq X] (P : Subgroup (Equiv.Perm X))
    (k : ℕ) (hk : IsMultiplyPretransitive P X k) (hAlt : alternatingGroup X ≤ P)
    (e : Fin k ↪ X) (S : Sylow 3 (stabilizer P e))
    (hfix : Nat.card (fixedPoints (image e S) X) = k)
    (hfree : ∀ q : P, q ∈ image e S → q ≠ 1 →
      ∀ x : X, x ∉ fixedPoints (image e S) X → q • x ≠ x) :
    Fintype.card X ≤ k + 3 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  by_contra hlarge
  obtain ⟨g, hgAlt, hgorder, _, hgfix⟩ :=
    exists_even_three_cycle X (by omega)
  let u : P := ⟨g, hAlt hgAlt⟩
  have hu : orderOf u = 3 := (Subgroup.orderOf_coe u).symm.trans hgorder
  have hufix : (fixedBy X u).ncard = Fintype.card X - 3 := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact hgfix
  have hexact := PrimeTupleSemiregularFixed.fixed_card P X k hk e S hfix hfree u hu (by omega)
  omega

end FiveTransitive.ThreeCycleSemiregularDegree

end CFSG

module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

open Equiv
open scoped Pointwise

theorem natCard_alternatingGroup_fin5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem four_eq_two_pow_factorization_alt5 :
    (4 : ℕ) = 2 ^ (Nat.card (alternatingGroup (Fin 5))).factorization 2 := by
  rw [natCard_alternatingGroup_fin5, Nat.factorization_def _ Nat.prime_two]
  have h1 : padicValNat 2 (2 ^ 2 * 15) = padicValNat 2 (2 ^ 2) + padicValNat 2 15 :=
    padicValNat.mul (by norm_num) (by norm_num)
  have h2 : padicValNat 2 (2 ^ 2) = 2 := padicValNat.prime_pow 2
  have h3 : padicValNat 2 15 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h60 : padicValNat 2 60 = 2 := by
    rw [show (60 : ℕ) = 2 ^ 2 * 15 by norm_num, h1, h2, h3]
  rw [h60]
  norm_num

theorem alt5_klein_conj (V W : Subgroup (Equiv.Perm (Fin 5)))
    (hV : V ≤ alternatingGroup (Fin 5)) (hW : W ≤ alternatingGroup (Fin 5))
    (hVc : Nat.card V = 4) (hWc : Nat.card W = 4) :
    ∃ g ∈ alternatingGroup (Fin 5), W = V.map (MulAut.conj g).toMonoidHom := by
  set A := alternatingGroup (Fin 5) with hA
  set V' : Subgroup A := V.subgroupOf A with hV'
  set W' : Subgroup A := W.subgroupOf A with hW'
  have hV'c : Nat.card V' = 4 := by
    rw [hV', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv, hVc]
  have hW'c : Nat.card W' = 4 := by
    rw [hW', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW).toEquiv, hWc]
  let P : Sylow 2 A := Sylow.ofCard V' (hV'c.trans four_eq_two_pow_factorization_alt5)
  let Q : Sylow 2 A := Sylow.ofCard W' (hW'c.trans four_eq_two_pow_factorization_alt5)
  obtain ⟨g, hg⟩ := (inferInstance : MulAction.IsPretransitive A (Sylow 2 A)).exists_smul_eq P Q
  have hcoe : (W' : Set A) = MulAut.conj g • (V' : Set A) := by
    have h : (Q : Set A) = MulAut.conj g • (P : Set A) := by
      rw [← hg, Sylow.coe_smul]
    exact h
  refine ⟨(g : Perm (Fin 5)), g.2, ?_⟩
  ext x
  constructor
  · intro hx
    have hxA : x ∈ A := hW hx
    have hxW' : (⟨x, hxA⟩ : A) ∈ (W' : Set A) := Subgroup.mem_subgroupOf.mpr hx
    rw [hcoe, Set.mem_smul_set] at hxW'
    obtain ⟨y, hy, hyx⟩ := hxW'
    refine (Subgroup.mem_map).mpr ⟨y.1, Subgroup.mem_subgroupOf.mp hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyA : y ∈ A := hV hy
    have hyV' : (⟨y, hyA⟩ : A) ∈ V' := Subgroup.mem_subgroupOf.mpr hy
    have hmem : (MulAut.conj g • (⟨y, hyA⟩ : A)) ∈ (W' : Set A) := by
      rw [hcoe]
      exact Set.smul_mem_smul_set hyV'
    have hW'mem : (MulAut.conj g • (⟨y, hyA⟩ : A)) ∈ W' := hmem
    have := Subgroup.mem_subgroupOf.mp hW'mem
    simpa [MulAut.smul_def, MulAut.conj_apply] using this

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

end

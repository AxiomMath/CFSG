module

public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.Open.Defs
import CFSG.CharacterTheory.Burnside
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
import Mathlib.GroupTheory.IsPerfect
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (gramForm_isSymm gramForm_separatingLeft unitarySU
  unitarySU_eq_gramSU card_gramSU)

private theorem not_isSolvable_of_quasisimple {X : Type*} [Group X]
    (hX : CFSG.Open.IsQuasisimple X) : ¬ Group.IsSolvable X := by
  haveI := hX.2.toNontrivial
  haveI : Nontrivial X := (QuotientGroup.mk_surjective (s := Subgroup.center X)).nontrivial
  haveI : Group.IsPerfect X := ⟨hX.1⟩
  exact Group.IsPerfect.not_isSolvable X

section Orders

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

private theorem natCard_su_zero : Nat.card ↥(SU (unitaryInvolution F 2 f) 0) = 1 := by
  haveI : Subsingleton ↥(SU (unitaryInvolution F 2 f) 0) :=
    ⟨fun _ _ => Subtype.ext (Units.ext (Matrix.ext fun i => i.elim0))⟩
  exact Nat.card_of_subsingleton 1

private theorem natCard_su (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {k : ℕ} (hk : 1 ≤ k) :
    (Nat.card ↥(SU (unitaryInvolution F 2 f) k) : ℤ) = ((2 ^ f : ℕ) : ℤ) ^ (k * (k - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 k, (((2 ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hU : UnitaryFieldData 2 f F := ⟨Nat.prime_two, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hord := (CFSG.LinearGroups.unitary_full_group_order hU
    (gramForm_isSymm hU (G := (1 : Matrix (Fin k) (Fin k) F)) (by simp))
    (gramForm_separatingLeft hU (by simp)) (Module.finrank_fin_fun F) hk).2.1
  rw [Nat.card_congr (CFSG.LieType.Universal.Unitary.equivStatedSU hF k).toEquiv,
    show CFSG.Open.StatedSU k (2 ^ f) F = unitarySU 2 f F k from rfl, unitarySU_eq_gramSU hU,
    card_gramSU, hord]

end Orders

theorem two_le_of_su_isQuasisimple {F : Type} [Field F] [Finite F] [CharP F 2] {f k : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {X : Type*} [Group X]
    (φ : ↥(SU (unitaryInvolution F 2 f) k) →* X) (hφ : Function.Surjective φ)
    (hX : CFSG.Open.IsQuasisimple X) : 2 ≤ k ∧ (k ≤ 3 → 2 ≤ f) := by
  have hns : ∀ a b : ℕ, Nat.card ↥(SU (unitaryInvolution F 2 f) k) ≠ 2 ^ a * 3 ^ b := by
    intro a b h
    haveI : Finite ↥(SU (unitaryInvolution F 2 f) k) :=
      Nat.finite_of_card_ne_zero (by rw [h]; positivity)
    have := Fintype.ofFinite ↥(SU (unitaryInvolution F 2 f) k)
    haveI := CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (G := ↥(SU (unitaryInvolution F 2 f) k)) Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, h])
    exact not_isSolvable_of_quasisimple hX (solvable_of_surjective hφ)
  rcases Nat.lt_or_ge k 2 with hk | hk
  · exfalso
    obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
    · exact hns 0 0 (by rw [natCard_su_zero]; rfl)
    · refine hns 0 0 ?_
      have h1 := natCard_su hF hf (k := 1) le_rfl
      rw [show Finset.Icc 2 1 = ∅ from by decide, Finset.prod_empty] at h1
      norm_num at h1 ⊢
      exact_mod_cast h1
  · refine ⟨hk, fun hk3 => ?_⟩
    by_contra hf2
    obtain rfl : f = 1 := by omega
    obtain rfl | rfl : k = 2 ∨ k = 3 := by omega
    · refine hns 1 1 ?_
      have h2 := natCard_su hF hf (k := 2) (by norm_num)
      rw [Finset.Icc_self, Finset.prod_singleton] at h2
      norm_num at h2 ⊢
      exact_mod_cast h2
    · refine hns 3 3 ?_
      have h3 := natCard_su hF hf (k := 3) (by norm_num)
      rw [show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by norm_num)] at h3
      norm_num at h3 ⊢
      exact_mod_cast h3

end CFSG.StandardType.SCFourCover

end

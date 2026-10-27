module

public import CFSG.Quasithin.Background.F7TwoInvL3TwoGen

public section

namespace CFSG.Quasithin.F7Two

open CFSG.CGT.Timmesfeld75 CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBGraphForm
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem invAutGen_fieldAut (hK : ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f) {σ : K ≃+* K}
    (hσ1 : σ ≠ 1) (hσ2 : ∀ x, σ (σ x) = x) :
    InvAutGen (projectiveSL 3 K) (fieldAut 3 K σ) :=
  invAutGen_of_blocks hK (sl2FieldAut_mul_self hσ2) (sl2FieldAut_ne_one hσ1)
    fun i g => fieldAut_sl3BlockRho i σ g

theorem invAutGen_dualAut (hK : ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f) :
    InvAutGen (projectiveSL 3 K) (dualAut 3 K) :=
  invAutGen_of_blocks hK slGraphAut_two_mul_self slGraphAut_two_ne_one
    fun i g => dualAut_sl3BlockRho i g

theorem invAutGen_fieldAut_mul_dualAut (hK : ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f)
    {σ : K ≃+* K} (hσ2 : ∀ x, σ (σ x) = x) :
    InvAutGen (projectiveSL 3 K) (fieldAut 3 K σ * dualAut 3 K) :=
  invAutGen_of_blocks hK (β := sl2FieldGraph σ) (sl2FieldGraph_mul_self hσ2)
    (sl2FieldGraph_ne_one σ) fun i g => by
      rw [MulAut.mul_apply, dualAut_sl3BlockRho, fieldAut_sl3BlockRho]
      rfl

theorem pow_pow_half_involutive {f : ℕ} (hf : Even f) (hK : Nat.card K = 2 ^ f) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 2 ^ (f / 2)) : ∀ x, σ (σ x) = x := by
  intro x
  obtain ⟨h, rfl⟩ := hf
  have h2 : (h + h) / 2 = h := by omega
  rw [hσ, hσ, h2, ← pow_mul, ← pow_add]
  have : Fintype K := Fintype.ofFinite K
  rw [← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

end CFSG.Quasithin.F7Two

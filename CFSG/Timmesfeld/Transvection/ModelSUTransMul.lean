module

public import CFSG.Timmesfeld.Transvection.ModelTransMul
public import CFSG.Timmesfeld.LieEmbed.UnitaryForms

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed

namespace ModelRank

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {m : ℕ}

theorem ne_one_pow_two_pow_of_uTrans_mul (hσ : ∀ c, σ (σ c) = c) {p q : Fin m → F}
    (hpp : uForm σ p p = 0) (hqq : uForm σ q q = 0) (hpq : uForm σ p q ≠ 0) {c c' : F}
    (hc : c ≠ 0) (hc' : c' ≠ 0) {g : SU σ m}
    (hg : suMat σ m g = uTrans σ p c * uTrans σ q c') (k : ℕ) : g ^ (2 ^ k) ≠ 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hqp : uForm σ q p ≠ 0 := by
    rw [← uForm_conj σ hσ p q]
    exact (map_ne_zero σ).2 hpq
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hpq (by simp [uForm_eq])
  have hMp : suMat σ m g *ᵥ p =
      (1 + c * c' * uForm σ q p * uForm σ p q) • p + (c' * uForm σ q p) • q := by
    rw [hg, ← mulVec_mulVec, uTrans_mulVec, uTrans_mulVec, uForm_add_right, hpp,
      uForm_smul_right]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hMq : suMat σ m g *ᵥ q = (c * uForm σ p q) • p + q := by
    rw [hg, ← mulVec_mulVec, uTrans_mulVec, uTrans_mulVec, hqq, mul_zero, zero_smul, add_zero,
      add_comm]
  have hQ : (suMat σ m g ^ 2 + 1) *ᵥ p =
      (c * c' * uForm σ q p * uForm σ p q) • (suMat σ m g *ᵥ p) := by
    rw [add_mulVec, one_mulVec, sq (suMat σ m g), ← mulVec_mulVec, hMp, mulVec_add,
      mulVec_smul, mulVec_smul, hMp, hMq]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination ((1 + c * c' * uForm σ q p * uForm σ p q) * p i +
      c' * uForm σ q p * q i) * h2
  have hτ : c * c' * uForm σ q p * uForm σ p q ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hc hc') hqp) hpq
  intro h1
  exact pow_two_pow_mulVec_ne_self hp0 hτ hQ k (by rw [← map_pow, h1, map_one, one_mulVec])

end ModelRank

end CFSG.Timmesfeld.Transvection

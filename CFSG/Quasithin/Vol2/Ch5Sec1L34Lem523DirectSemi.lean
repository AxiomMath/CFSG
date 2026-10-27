module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectGal

public section

namespace CFSG.Quasithin.H13.Direct523Semi

variable {K : Type} [Field K]

@[expose] def e₁ : Fin 2 → K := ![1, 0]

@[expose] def e₂ : Fin 2 → K := ![0, 1]

theorem decomp (w : Fin 2 → K) : w = w 0 • e₁ + w 1 • e₂ := by
  funext i
  fin_cases i <;> simp [e₁, e₂]

@[expose] def IsSemi (B : (Fin 2 → K) ≃+ (Fin 2 → K)) (σ : K ≃+* K) : Prop :=
  ∀ (a : K) (w : Fin 2 → K), B (a • w) = σ a • B w

theorem IsSemi.smul {B : (Fin 2 → K) ≃+ (Fin 2 → K)} {σ : K ≃+* K} (hB : IsSemi B σ)
    (a : K) (w : Fin 2 → K) : B (a • w) = σ a • B w := hB a w

theorem IsSemi.apply {B : (Fin 2 → K) ≃+ (Fin 2 → K)} {σ : K ≃+* K} (hB : IsSemi B σ)
    (w : Fin 2 → K) : B w = σ (w 0) • B e₁ + σ (w 1) • B e₂ := by
  conv_lhs => rw [decomp w]
  rw [map_add, hB, hB]

@[expose]
def uB (β : K) : (Fin 2 → K) ≃+ (Fin 2 → K) where
  toFun w := ![w 0 + β * w 1, w 1]
  invFun w := ![w 0 - β * w 1, w 1]
  left_inv w := by
    funext i
    fin_cases i <;> simp
  right_inv w := by
    funext i
    fin_cases i <;> simp
  map_add' v w := by
    funext i
    fin_cases i <;> simp <;> ring

theorem uB_e₂ (β : K) : uB β e₂ = β • e₁ + e₂ := by
  funext i
  fin_cases i <;> simp [uB, e₁, e₂]

theorem semi_e₁ {B : (Fin 2 → K) ≃+ (Fin 2 → K)} {σ : K ≃+* K} (hB : IsSemi B σ) {a₀ : K}
    (ha₀ : a₀ ≠ 0) (hfix : B (a₀ • e₁) = a₀ • e₁) :
    B e₁ = (a₀ * (σ a₀)⁻¹) • e₁ := by
  have h1 : σ a₀ • B e₁ = a₀ • e₁ := by
    rw [← hB, hfix]
  have hσ : σ a₀ ≠ 0 := by
    intro h
    have := map_eq_zero_iff σ σ.injective |>.mp h
    exact ha₀ this
  calc B e₁ = (σ a₀)⁻¹ • (σ a₀ • B e₁) := by rw [smul_smul, inv_mul_cancel₀ hσ, one_smul]
    _ = (σ a₀)⁻¹ • (a₀ • e₁) := by rw [h1]
    _ = (a₀ * (σ a₀)⁻¹) • e₁ := by rw [smul_smul, mul_comm]

theorem semi_aut_cases [Finite K] (hK : Nat.card K = 4) [CharP K 2] (σ : K ≃+* K) :
    σ = RingEquiv.refl K ∨ ∀ x : K, σ x = x ^ 2 := by
  obtain ⟨i, hi⟩ := Direct523Gal.exists_pow_two_pow σ
  have h4 : ∀ y : K, y ^ 4 = y := fun y => by
    have := Direct523Gal.pow_natCard y
    rwa [hK] at this
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' i
  · left
    ext x
    rw [hi, hj, RingEquiv.refl_apply, show (2 : ℕ) ^ (2 * j) = 4 ^ j by rw [pow_mul]; norm_num]
    exact Direct523Gal.pow_four_pow (h4 x) j
  · right
    intro x
    rw [hi, hj, show (2 : ℕ) ^ (2 * j + 1) = 2 * 4 ^ j by rw [pow_succ, pow_mul]; norm_num; ring,
      pow_mul]
    exact Direct523Gal.pow_four_pow (h4 (x ^ 2)) j

theorem lin_apply {B : (Fin 2 → K) ≃+ (Fin 2 → K)} (hB : IsSemi B (RingEquiv.refl K))
    (w : Fin 2 → K) : B w = w 0 • B e₁ + w 1 • B e₂ := by
  simpa using IsSemi.apply hB w

theorem uB_apply (β : K) (w : Fin 2 → K) : uB β w = ![w 0 + β * w 1, w 1] := rfl

theorem linear_eq_uB [CharP K 2] {B : (Fin 2 → K) ≃+ (Fin 2 → K)} {a₀ : K} (ha₀ : a₀ ≠ 0)
    (hB : IsSemi B (RingEquiv.refl K)) (hfix : B (a₀ • e₁) = a₀ • e₁)
    (hinv : ∀ w, B (B w) = w) : ∃ β : K, B = uB β := by
  have hBe1 : B e₁ = e₁ := by
    rw [semi_e₁ hB ha₀ hfix, RingEquiv.refl_apply, mul_inv_cancel₀ ha₀, one_smul]
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨b, d, hBe2⟩ : ∃ b d : K, B e₂ = b • e₁ + d • e₂ :=
    ⟨B e₂ 0, B e₂ 1, decomp (B e₂)⟩
  have hd : d * d = 1 := by
    have h := hinv e₂
    rw [lin_apply hB (B e₂), hBe1, hBe2] at h
    simpa [e₁, e₂] using congrFun h 1
  have hd1 : d = 1 := by
    have h3 : (d - 1) * (d - 1) = 0 := by linear_combination hd + (1 - d) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  refine ⟨b, AddEquiv.ext fun w => ?_⟩
  rw [lin_apply hB w, hBe1, hBe2, hd1, uB_apply]
  funext i
  fin_cases i <;> simp [e₁, e₂] <;> ring

end CFSG.Quasithin.H13.Direct523Semi

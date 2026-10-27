module

public import CFSG.Quasithin.Background.F918Z3Cg2Par
public import CFSG.Quasithin.Background.F918Z2Norm
public import CFSG.Quasithin.Background.F918Z3CaSemi
public import CFSG.Quasithin.Background.F918Z3Cg2Fix

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace Z3Cg2

section Counting

variable {V : Type} [CommGroup V] [Finite V]

theorem le_rkIdx_of_card_mul_le (hexp : ∀ v : V, v ^ 2 = 1) (H : Subgroup V) {k : ℕ}
    (h : Nat.card H * 2 ^ k ≤ Nat.card V) : k ≤ rkIdx H := by
  have h1 : Nat.card H = 2 ^ rk H := card_eq_two_pow hexp H
  have h2 : Nat.card V = 2 ^ rk V := card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hexp)
  have h3 := rk_add_rkIdx H
  rw [h1, h2, ← pow_add] at h
  have h4 : rk H + k ≤ rk V := (Nat.pow_le_pow_iff_right (by norm_num)).1 h
  omega

theorem eight_a_le_rkIdx (hexp : ∀ v : V, v ^ 2 = 1) (H : Subgroup V) {a : ℕ}
    (hV : Nat.card V = 2 ^ (16 * a)) (h : Nat.card H ^ 2 = Nat.card V) : 8 * a ≤ rkIdx H := by
  have h2 : Nat.card H = 2 ^ (8 * a) := by
    have h3 : Nat.card H ^ 2 = (2 ^ (8 * a)) ^ 2 := by
      rw [h, hV, ← pow_mul]
      ring_nf
    exact Nat.pow_left_injective (by norm_num) h3
  refine le_rkIdx_of_card_mul_le hexp H ?_
  rw [h2, ← pow_add, hV]
  exact le_of_eq (by ring_nf)

end Counting

section Linear

variable {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}

theorem exists_involutions_of_sq (hd : 0 < d) {B₁ B₂ : Matrix (Fin d) (Fin d) F}
    (hinv : ∀ M : Matrix (Fin d) (Fin d) F, B₁ * (B₁ * M * B₂) * B₂ = M) :
    ∃ P Q : Matrix (Fin d) (Fin d) F, P * P = 1 ∧ Q * Q = 1 ∧
      ∀ M, B₁ * M * B₂ = P * M * Qᵀ := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hCE : ∀ M : Matrix (Fin d) (Fin d) F, (B₁ * B₁) * M * (B₂ * B₂) = M := fun M => by
    have h := hinv M
    simpa only [Matrix.mul_assoc] using h
  have h1 : (B₁ * B₁) * (B₂ * B₂) = 1 := by simpa using hCE 1
  have h2 : (B₂ * B₂) * (B₁ * B₁) = 1 := mul_eq_one_comm.1 h1
  have hCM : ∀ M : Matrix (Fin d) (Fin d) F, (B₁ * B₁) * M = M * (B₁ * B₁) := fun M => by
    calc (B₁ * B₁) * M = (B₁ * B₁) * M * ((B₂ * B₂) * (B₁ * B₁)) := by rw [h2, Matrix.mul_one]
      _ = ((B₁ * B₁) * M * (B₂ * B₂)) * (B₁ * B₁) := by simp only [Matrix.mul_assoc]
      _ = M * (B₁ * B₁) := by rw [hCE]
  obtain ⟨c, hc⟩ : (B₁ * B₁) ∈
      Set.range (Matrix.scalar (Fin d) : F →+* Matrix (Fin d) (Fin d) F) :=
    Matrix.mem_range_scalar_of_commute_single fun i j _ => (hCM _).symm
  have hc' : B₁ * B₁ = c • (1 : Matrix (Fin d) (Fin d) F) := by
    rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [hc', zero_smul, zero_mul] at h1
    exact zero_ne_one h1
  have hE : B₂ * B₂ = c⁻¹ • (1 : Matrix (Fin d) (Fin d) F) := by
    rw [hc', Matrix.smul_mul, Matrix.one_mul] at h1
    calc B₂ * B₂ = c⁻¹ • (c • (B₂ * B₂)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • 1 := by rw [h1]
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' c
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [hμ, mul_zero])
  refine ⟨μ⁻¹ • B₁, μ • B₂ᵀ, ?_, ?_, fun M => ?_⟩
  · calc (μ⁻¹ • B₁) * (μ⁻¹ • B₁) = (μ⁻¹ * μ⁻¹) • (B₁ * B₁) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = (μ⁻¹ * μ⁻¹ * (μ * μ)) • (1 : Matrix (Fin d) (Fin d) F) := by rw [hc', smul_smul, ← hμ]
      _ = 1 := by
          have : μ⁻¹ * μ⁻¹ * (μ * μ) = 1 := by field_simp
          rw [this, one_smul]
  · calc (μ • B₂ᵀ) * (μ • B₂ᵀ) = (μ * μ) • (B₂ * B₂)ᵀ := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.transpose_mul]
      _ = c • (c⁻¹ • (1 : Matrix (Fin d) (Fin d) F)) := by
          rw [hE, Matrix.transpose_smul, Matrix.transpose_one, ← hμ]
      _ = 1 := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
  · symm
    calc (μ⁻¹ • B₁) * M * (μ • B₂ᵀ)ᵀ = (μ⁻¹ • B₁) * M * (μ • B₂) := by
          rw [Matrix.transpose_smul, Matrix.transpose_transpose]
      _ = (μ * μ⁻¹) • (B₁ * M * B₂) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, mul_comm μ μ⁻¹]
      _ = B₁ * M * B₂ := by rw [mul_inv_cancel₀ hμ0, one_smul]

end Linear

section Dichotomy

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)}
  {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ}
  {β : V ≃* Multiplicative (Matrix (Fin d) (Fin d) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin d) F}

theorem normalizer_dichotomy (hM : IsMatModel D X β ρ σ) (hd : 0 < d) {b : MulAut V}
    (hbb : b * b = 1) (hbD : D.map (MulAut.conj b).toMonoidHom = D)
    (hbX : X.map (MulAut.conj b).toMonoidHom = X) :
    Nat.card ↥(fixV (Subgroup.zpowers b)) ^ 2 = Nat.card V ∨
      ∃ P Q : Matrix (Fin d) (Fin d) F, P * P = 1 ∧ Q * Q = 1 ∧
        ∀ v : V, Multiplicative.toAdd (β (b v)) = P * Multiplicative.toAdd (β v) * Qᵀ := by
  obtain ⟨ϑ, B₁, B₂, hB₁, hB₂, hb⟩ := normalizer_form_of_sqModel hM hd hbD hbX
  have hinv : ∀ M : Matrix (Fin d) (Fin d) F, B₁ * (B₁ * M.map ϑ * B₂).map ϑ * B₂ = M := by
    intro M
    obtain ⟨v, hv⟩ : ∃ v, Multiplicative.toAdd (β v) = M :=
      ⟨β.symm (Multiplicative.ofAdd M), by simp⟩
    have h3 : b (b v) = v := by simpa using congrArg (fun f : MulAut V => f v) hbb
    have h2 := hb (b v)
    rw [h3, hb v, hv] at h2
    exact h2.symm
  by_cases hϑ : ϑ = RingEquiv.refl F
  · right
    subst hϑ
    have hmap : ∀ M : Matrix (Fin d) (Fin d) F, M.map (RingEquiv.refl F) = M := fun M => by
      ext i j
      rfl
    simp only [hmap] at hinv hb
    obtain ⟨P, Q, hP, hQ, hPQ⟩ := exists_involutions_of_sq hd hinv
    exact ⟨P, Q, hP, hQ, fun v => by rw [hb v, hPQ]⟩
  · left
    have h := card_fixed_semilinear hϑ hB₁ hB₂ hinv
    rw [card_fixV_zpowers_eq β b (fun M => B₁ * M.map ϑ * B₂) hb, h, card_V_eq β]

omit [Finite F] in
theorem card_fixV_mul_le {P Q : Matrix (Fin d) (Fin d) F} {b : MulAut V}
    (hb : ∀ v : V, Multiplicative.toAdd (β (b v)) = P * Multiplicative.toAdd (β v) * Qᵀ) {t : ℕ}
    (ht : Nat.card F ^ t ≤ Nat.card (Set.range fun M : Matrix (Fin d) (Fin d) F =>
      M + P * M * Qᵀ)) :
    Nat.card ↥(fixV (Subgroup.zpowers b)) * Nat.card F ^ t ≤ Nat.card V := by
  have hV : Nat.card V = Nat.card (Matrix (Fin d) (Fin d) F) := by
    rw [Nat.card_congr β.toEquiv, Nat.card_congr Multiplicative.toAdd]
  have hprod := AddSubgroup.card_ker_mul_card_range (InvolMat.sumHom P Q)
  have hker : Nat.card {M : Matrix (Fin d) (Fin d) F // P * M * Qᵀ = M} =
      Nat.card (InvolMat.sumHom P Q).ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun M => (InvolMat.mem_ker_sumHom M).symm)
  have hrange : Nat.card (Set.range fun M : Matrix (Fin d) (Fin d) F => M + P * M * Qᵀ) =
      Nat.card (InvolMat.sumHom P Q).range := rfl
  rw [card_fixV_zpowers_eq β b (fun M => P * M * Qᵀ) hb, hV, ← hprod, hker, ← hrange]
  exact Nat.mul_le_mul_left _ ht

end Dichotomy

end Z3Cg2

end CFSG.Quasithin

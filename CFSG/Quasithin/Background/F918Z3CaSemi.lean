module

public import CFSG.Quasithin.Background.F918Z3Ca

public section

namespace CFSG.Quasithin

open scoped Matrix

namespace InvolMat

@[expose] def semiHom {F : Type} [Field F] {d : ℕ} (ϑ : F ≃+* F)
    (B₁ B₂ : Matrix (Fin d) (Fin d) F) : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F :=
  AddMonoidHom.mk' (fun M => B₁ * M.map ϑ * B₂) (by
    intro a b
    simp only [Matrix.map_add _ (map_add ϑ), mul_add, add_mul])

theorem semiHom_apply {F : Type} [Field F] {d : ℕ} (ϑ : F ≃+* F)
    (B₁ B₂ M : Matrix (Fin d) (Fin d) F) : semiHom ϑ B₁ B₂ M = B₁ * M.map ϑ * B₂ := rfl

theorem semiHom_smul {F : Type} [Field F] {d : ℕ} (ϑ : F ≃+* F)
    (B₁ B₂ M : Matrix (Fin d) (Fin d) F) (c : F) :
    semiHom ϑ B₁ B₂ (c • M) = ϑ c • semiHom ϑ B₁ B₂ M := by
  have : (c • M).map ϑ = ϑ c • M.map ϑ := by
    ext i j
    simp
  rw [semiHom_apply, semiHom_apply, this, Matrix.mul_smul, Matrix.smul_mul]

@[expose] def semiSumHom {F : Type} [Field F] {d : ℕ} (ϑ : F ≃+* F)
    (B₁ B₂ : Matrix (Fin d) (Fin d) F) : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F :=
  AddMonoidHom.id _ + semiHom ϑ B₁ B₂

theorem semiSumHom_apply {F : Type} [Field F] {d : ℕ} (ϑ : F ≃+* F)
    (B₁ B₂ M : Matrix (Fin d) (Fin d) F) :
    semiSumHom ϑ B₁ B₂ M = M + B₁ * M.map ϑ * B₂ := rfl

theorem semiSumHom_semiSumHom {F : Type} [Field F] [CharP F 2] {d : ℕ} {ϑ : F ≃+* F}
    {B₁ B₂ : Matrix (Fin d) (Fin d) F}
    (hinv : ∀ M : Matrix (Fin d) (Fin d) F, B₁ * (B₁ * M.map ϑ * B₂).map ϑ * B₂ = M)
    (M : Matrix (Fin d) (Fin d) F) : semiSumHom ϑ B₁ B₂ (semiSumHom ϑ B₁ B₂ M) = 0 := by
  have hM : semiHom ϑ B₁ B₂ (semiHom ϑ B₁ B₂ M) = M := hinv M
  have e1 : M + M = 0 := add_self_eq_zero F M
  have e2 : semiHom ϑ B₁ B₂ M + semiHom ϑ B₁ B₂ M = 0 := add_self_eq_zero F _
  have : semiSumHom ϑ B₁ B₂ (semiSumHom ϑ B₁ B₂ M) =
      (M + M) + (semiHom ϑ B₁ B₂ M + semiHom ϑ B₁ B₂ M) := by
    simp only [semiSumHom, AddMonoidHom.add_apply, AddMonoidHom.id_apply, map_add, hM]
    abel
  rw [this, e1, e2, add_zero]

theorem mem_ker_semiSumHom {F : Type} [Field F] [CharP F 2] {d : ℕ} {ϑ : F ≃+* F}
    {B₁ B₂ : Matrix (Fin d) (Fin d) F} (M : Matrix (Fin d) (Fin d) F) :
    M ∈ (semiSumHom ϑ B₁ B₂).ker ↔ B₁ * M.map ϑ * B₂ = M := by
  rw [AddMonoidHom.mem_ker, semiSumHom_apply, add_eq_zero_iff_eq_neg, neg_eq_self F]
  exact eq_comm

theorem semi_involutive {F : Type} [Field F] {d : ℕ} (hd : 0 < d) {ϑ : F ≃+* F}
    {B₁ B₂ : Matrix (Fin d) (Fin d) F}
    (hinv : ∀ M : Matrix (Fin d) (Fin d) F, B₁ * (B₁ * M.map ϑ * B₂).map ϑ * B₂ = M)
    (c : F) : ϑ (ϑ c) = c := by
  have h1 : semiHom ϑ B₁ B₂ (semiHom ϑ B₁ B₂ (1 : Matrix (Fin d) (Fin d) F)) = 1 := hinv 1
  have h2 : semiHom ϑ B₁ B₂ (semiHom ϑ B₁ B₂ (c • (1 : Matrix (Fin d) (Fin d) F))) =
      c • (1 : Matrix (Fin d) (Fin d) F) := hinv _
  rw [semiHom_smul, semiHom_smul, h1] at h2
  have := congrFun (congrFun h2 ⟨0, hd⟩) ⟨0, hd⟩
  simpa using this

theorem exists_add_eq_one {F : Type} [Field F] [CharP F 2] {ϑ : F ≃+* F}
    (hϑ : ϑ ≠ RingEquiv.refl F) (hinv : ∀ x, ϑ (ϑ x) = x) : ∃ ε : F, ε + ϑ ε = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, ϑ x ≠ x := by
    by_contra h
    push Not at h
    exact hϑ (RingEquiv.ext h)
  have hc0 : x + ϑ x ≠ 0 := by
    intro h
    apply hx
    have := eq_neg_of_add_eq_zero_right h
    rw [this, neg_eq_self F]
  have hc : ϑ (x + ϑ x) = x + ϑ x := by
    rw [map_add, hinv, add_comm]
  refine ⟨x * (x + ϑ x)⁻¹, ?_⟩
  rw [map_mul, map_inv₀, hc, ← add_mul]
  exact mul_inv_cancel₀ hc0

theorem ker_semiSumHom_eq_range {F : Type} [Field F] [CharP F 2] {d : ℕ} {ϑ : F ≃+* F}
    (hϑ : ϑ ≠ RingEquiv.refl F) {B₁ B₂ : Matrix (Fin d) (Fin d) F}
    (hinv : ∀ M : Matrix (Fin d) (Fin d) F, B₁ * (B₁ * M.map ϑ * B₂).map ϑ * B₂ = M) :
    (semiSumHom ϑ B₁ B₂).ker = (semiSumHom ϑ B₁ B₂).range := by
  refine le_antisymm (fun M hM => ?_) ?_
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact ⟨0, Matrix.ext fun i => i.elim0⟩
    · obtain ⟨ε, hε⟩ := exists_add_eq_one hϑ (semi_involutive hd hinv)
      have hfix : semiHom ϑ B₁ B₂ M = M := (mem_ker_semiSumHom M).1 hM
      refine ⟨ε • M, ?_⟩
      rw [semiSumHom, AddMonoidHom.add_apply, AddMonoidHom.id_apply, semiHom_smul, hfix,
        ← add_smul, hε, one_smul]
  · rintro _ ⟨N, rfl⟩
    exact semiSumHom_semiSumHom hinv N

end InvolMat

open InvolMat

theorem card_fixed_semilinear {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ} {ϑ : F ≃+* F}
    (hϑ : ϑ ≠ RingEquiv.refl F) {B₁ B₂ : Matrix (Fin d) (Fin d) F} (_hB₁ : IsUnit B₁)
    (_hB₂ : IsUnit B₂)
    (hinv : ∀ M : Matrix (Fin d) (Fin d) F, B₁ * (B₁ * M.map ϑ * B₂).map ϑ * B₂ = M) :
    Nat.card {M : Matrix (Fin d) (Fin d) F // B₁ * M.map ϑ * B₂ = M} ^ 2 =
      Nat.card F ^ (d * d) := by
  have h := card_ker_sq_of_ker_eq_range _ (ker_semiSumHom_eq_range hϑ hinv)
  rw [card_matrix F d] at h
  rw [← h]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun M => (mem_ker_semiSumHom M).symm)

end CFSG.Quasithin

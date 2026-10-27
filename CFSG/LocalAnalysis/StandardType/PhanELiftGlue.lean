module

public import CFSG.ClassicalInvolution.Phan.Coherent

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {X : Type} [Group X]

private lemma hmbGlue_rotMat_mul_self {F : Type*} [Field F] :
    (rotMat : Matrix (Fin 2) (Fin 2) F) * rotMat = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMat, Matrix.mul_apply, Fin.sum_univ_two]

private lemma hmbGlue_rotMatInv_mul_self {F : Type*} [Field F] :
    (rotMatInv : Matrix (Fin 2) (Fin 2) F) * rotMatInv = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotMatInv, Matrix.mul_apply, Fin.sum_univ_two]

private lemma hmbGlue_rot_rot {F : Type*} [Field F] (σ : F ≃+* F) (X : SUid σ 2) :
    rotSU σ * (rotSU σ * X * (rotSU σ)⁻¹) * (rotSU σ)⁻¹ = X := by
  apply Subtype.ext
  apply Units.ext
  change rotMat * (rotMat * ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * rotMatInv) *
      rotMatInv = ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  calc rotMat * (rotMat * ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * rotMatInv) *
        rotMatInv
      = (rotMat * rotMat) * ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (rotMatInv * rotMatInv) := by noncomm_ring
    _ = (-1) * ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (-1) := by
        rw [hmbGlue_rotMat_mul_self, hmbGlue_rotMatInv_mul_self]
    _ = ((X : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by simp

theorem exists_glue_mirror (hK : Nat.card K = (p ^ f) ^ 2) {θ₁ θ₂ : Su K p f 3 →* X}
    (h₁ : θ₁.ker ≤ Subgroup.center (Su K p f 3)) (h₂ : θ₂.ker ≤ Subgroup.center (Su K p f 3))
    (hM : (B12 K p f).map θ₁ = (B23 K p f).map θ₂)
    (hcomm : ∀ x ∈ (B23 K p f).map θ₁, ∀ y ∈ (B12 K p f).map θ₂, x * y = y * x) :
    ∃ θ : Su K p f 3 →* X, θ.ker ≤ Subgroup.center (Su K p f 3) ∧ θ.range = θ₂.range ∧
      (B12 K p f).map θ = (B12 K p f).map θ₂ ∧ (B23 K p f).map θ = (B23 K p f).map θ₂ ∧
      θ.comp (embSUid (unitaryInvolution K p f) 0) =
        θ₁.comp (embSUid (unitaryInvolution K p f) 2) := by
  set σ : K ≃+* K := unitaryInvolution K p f
  let ω : Su K p f 3 ≃* Su K p f 3 := MulAut.conj (swapElt K p f)
  let A : Su K p f 3 →* X := θ₁.comp ω.toMonoidHom
  let B : Su K p f 3 →* X := θ₂.comp ω.toMonoidHom
  have hAker : A.ker ≤ Subgroup.center (Su K p f 3) := ker_comp_mulEquiv_le_center h₁ ω
  have hBker : B.ker ≤ Subgroup.center (Su K p f 3) := ker_comp_mulEquiv_le_center h₂ ω
  have hA12 : (B12 K p f).map A = (B23 K p f).map θ₁ := by
    change (B12 K p f).map (θ₁.comp ω.toMonoidHom) = (B23 K p f).map θ₁
    rw [map_comp_mulEquiv, map_conj_swapElt_B12]
  have hA23 : (B23 K p f).map A = (B12 K p f).map θ₁ := by
    change (B23 K p f).map (θ₁.comp ω.toMonoidHom) = (B12 K p f).map θ₁
    rw [map_comp_mulEquiv, map_conj_swapElt_B23]
  have hB12 : (B12 K p f).map B = (B23 K p f).map θ₂ := by
    change (B12 K p f).map (θ₂.comp ω.toMonoidHom) = (B23 K p f).map θ₂
    rw [map_comp_mulEquiv, map_conj_swapElt_B12]
  have hB23 : (B23 K p f).map B = (B12 K p f).map θ₂ := by
    change (B23 K p f).map (θ₂.comp ω.toMonoidHom) = (B12 K p f).map θ₂
    rw [map_comp_mulEquiv, map_conj_swapElt_B23]
  have hMAB : (B23 K p f).map A = (B12 K p f).map B := hA23.trans (hM.trans hB12.symm)
  have hcommAB : ∀ x ∈ (B12 K p f).map A, ∀ y ∈ (B23 K p f).map B, x * y = y * x := by
    intro x hx y hy
    rw [hA12] at hx
    rw [hB23] at hy
    exact hcomm x hx y hy
  obtain ⟨θ', hk', hr', h12', h23', hcomp⟩ :=
    exists_glue hK (autExtends hK) hAker hBker hMAB hcommAB
  have hω0 : ∀ Y : Su K p f 2,
      ω (embSUid σ 0 Y) = embSUid σ 2 (rotSU σ * Y * (rotSU σ)⁻¹) := by
    intro Y
    change (MulAut.conj (swapElt K p f)) (embSUid σ 0 Y) = _
    rw [MulAut.conj_apply]
    exact swapSU_mul_embSUid_zero_mul_inv σ Y
  refine ⟨θ'.comp ω.toMonoidHom, ker_comp_mulEquiv_le_center hk' ω,
    (range_comp_mulEquiv θ' ω).trans (hr'.trans (range_comp_mulEquiv θ₂ ω)), ?_, ?_,
    MonoidHom.ext fun Y => ?_⟩
  · change (B12 K p f).map (θ'.comp ω.toMonoidHom) = (B12 K p f).map θ₂
    rw [map_comp_mulEquiv, map_conj_swapElt_B12, h23', hB23]
  · change (B23 K p f).map (θ'.comp ω.toMonoidHom) = (B23 K p f).map θ₂
    rw [map_comp_mulEquiv, map_conj_swapElt_B23, h12', hB12]
  · change θ' (ω (embSUid σ 0 Y)) = θ₁ (embSUid σ 2 Y)
    rw [hω0 Y]
    have h2 : θ' (embSUid σ 2 (rotSU σ * Y * (rotSU σ)⁻¹)) =
        A (embSUid σ 0 (rotSU σ * Y * (rotSU σ)⁻¹)) := DFunLike.congr_fun hcomp _
    rw [h2]
    change θ₁ (ω (embSUid σ 0 (rotSU σ * Y * (rotSU σ)⁻¹))) = θ₁ (embSUid σ 2 Y)
    rw [hω0]
    rw [hmbGlue_rot_rot σ Y]

end CFSG.ClassicalInvolution.Phan.PhanE

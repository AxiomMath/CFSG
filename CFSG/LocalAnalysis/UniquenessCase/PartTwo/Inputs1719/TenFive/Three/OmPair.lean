module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmHeisHom
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmVec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmIso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

private theorem eMat_heis_pair_commute
    (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)
    {u₁ u₂ z₁ z₂ z₃ y₁ y₂ : Fin d → K} (hu₁ : Q u₁ = 0) (hu₂ : Q u₂ = 0)
    (h12 : polar Q u₁ u₂ = 0) (hz₁ : polar Q u₁ z₁ = 0) (hz₁' : polar Q u₂ z₁ = 0)
    (hz₂ : polar Q u₁ z₂ = 0) (hz₂' : polar Q u₂ z₂ = 0) (h₃₁ : polar Q u₁ z₃ = 0)
    (h₃₂ : polar Q u₂ z₃ = 0) (hy₁ : polar Q u₁ y₁ = 0) (hy₂ : polar Q u₂ y₁ = 0)
    (hy₂₁ : polar Q u₁ y₂ = 0) (hy₂₂ : polar Q u₂ y₂ = 0) (h₁y : polar Q z₁ y₂ = 0)
    (hy₁₃ : polar Q y₁ z₃ = 0) (h₂₃ : polar Q z₂ z₃ = 0) (a b c a' b' c' : K) :
    Commute (eMat hex u₂ (b • y₁) * (eMat hex u₁ (a • z₁) * eMat hex u₂ (a • z₂)) *
        eMat hex u₁ (c • u₂))
      (eMat hex u₂ (b' • y₂) * eMat hex u₁ (a' • z₃) * eMat hex u₁ (c' • u₂)) := by
  have hL1R1 : Commute (eMat hex u₂ (b • y₁)) (eMat hex u₂ (b' • y₂)) :=
    eMat_commute_same hex (by rw [polar_smul_right_eq, hy₂, mul_zero])
      (by rw [polar_smul_right_eq, hy₂₂, mul_zero])
  have hL1R2 : Commute (eMat hex u₂ (b • y₁)) (eMat hex u₁ (a' • z₃)) :=
    (eMat_commute_of_polar_eq_zero hex (e₁ := u₁) (e₂ := u₂) (w := a' • z₃) (w' := b • y₁)
      hu₂ h12
      (by rw [polar_smul_left_eq, polar_smul_right_eq, polar_comm, hy₁₃, mul_zero, mul_zero])
      (by rw [polar_smul_right_eq, h₃₁, mul_zero])
      (by rw [polar_smul_right_eq, h₃₂, mul_zero])
      (by rw [polar_smul_right_eq, hy₁, mul_zero])
      (by rw [polar_smul_right_eq, hy₂, mul_zero])).symm
  have hL1R4 : Commute (eMat hex u₂ (b • y₁)) (eMat hex u₁ (c' • u₂)) :=
    (eMat_center_commute_Y hex hu₁ hu₂ h12 (by rw [polar_smul_right_eq, hy₂, mul_zero]) c').symm
  have hL2R1 : Commute (eMat hex u₁ (a • z₁)) (eMat hex u₂ (b' • y₂)) :=
    eMat_commute_of_polar_eq_zero hex (e₁ := u₁) (e₂ := u₂) (w := a • z₁) (w' := b' • y₂)
      hu₂ h12
      (by rw [polar_smul_left_eq, polar_smul_right_eq, h₁y, mul_zero, mul_zero])
      (by rw [polar_smul_right_eq, hz₁, mul_zero])
      (by rw [polar_smul_right_eq, hz₁', mul_zero])
      (by rw [polar_smul_right_eq, hy₂₁, mul_zero])
      (by rw [polar_smul_right_eq, hy₂₂, mul_zero])
  have hL2R2 : Commute (eMat hex u₁ (a • z₁)) (eMat hex u₁ (a' • z₃)) :=
    eMat_commute_same hex (by rw [polar_smul_right_eq, hz₁, mul_zero])
      (by rw [polar_smul_right_eq, h₃₁, mul_zero])
  have hL2R4 : Commute (eMat hex u₁ (a • z₁)) (eMat hex u₁ (c' • u₂)) :=
    eMat_commute_same hex (by rw [polar_smul_right_eq, hz₁, mul_zero])
      (by rw [polar_smul_right_eq, h12, mul_zero])
  have hL3R1 : Commute (eMat hex u₂ (a • z₂)) (eMat hex u₂ (b' • y₂)) :=
    eMat_commute_same hex (by rw [polar_smul_right_eq, hz₂', mul_zero])
      (by rw [polar_smul_right_eq, hy₂₂, mul_zero])
  have hL3R2 : Commute (eMat hex u₂ (a • z₂)) (eMat hex u₁ (a' • z₃)) :=
    (eMat_commute_of_polar_eq_zero hex (e₁ := u₁) (e₂ := u₂) (w := a' • z₃) (w' := a • z₂)
      hu₂ h12
      (by rw [polar_smul_left_eq, polar_smul_right_eq, polar_comm, h₂₃, mul_zero, mul_zero])
      (by rw [polar_smul_right_eq, h₃₁, mul_zero])
      (by rw [polar_smul_right_eq, h₃₂, mul_zero])
      (by rw [polar_smul_right_eq, hz₂, mul_zero])
      (by rw [polar_smul_right_eq, hz₂', mul_zero])).symm
  have hL3R4 : Commute (eMat hex u₂ (a • z₂)) (eMat hex u₁ (c' • u₂)) :=
    (eMat_center_commute_Y hex hu₁ hu₂ h12 (by rw [polar_smul_right_eq, hz₂', mul_zero]) c').symm
  have hL4R1 : Commute (eMat hex u₁ (c • u₂)) (eMat hex u₂ (b' • y₂)) :=
    eMat_center_commute_Y hex hu₁ hu₂ h12 (by rw [polar_smul_right_eq, hy₂₂, mul_zero]) c
  have hL4R2 : Commute (eMat hex u₁ (c • u₂)) (eMat hex u₁ (a' • z₃)) :=
    eMat_commute_same hex (by rw [polar_smul_right_eq, h12, mul_zero])
      (by rw [polar_smul_right_eq, h₃₁, mul_zero])
  have hL4R4 : Commute (eMat hex u₁ (c • u₂)) (eMat hex u₁ (c' • u₂)) :=
    eMat_commute_same hex (by rw [polar_smul_right_eq, h12, mul_zero])
      (by rw [polar_smul_right_eq, h12, mul_zero])
  have hL1 : Commute (eMat hex u₂ (b • y₁))
      (eMat hex u₂ (b' • y₂) * eMat hex u₁ (a' • z₃) * eMat hex u₁ (c' • u₂)) :=
    (hL1R1.mul_right hL1R2).mul_right hL1R4
  have hL2 : Commute (eMat hex u₁ (a • z₁))
      (eMat hex u₂ (b' • y₂) * eMat hex u₁ (a' • z₃) * eMat hex u₁ (c' • u₂)) :=
    (hL2R1.mul_right hL2R2).mul_right hL2R4
  have hL3 : Commute (eMat hex u₂ (a • z₂))
      (eMat hex u₂ (b' • y₂) * eMat hex u₁ (a' • z₃) * eMat hex u₁ (c' • u₂)) :=
    (hL3R1.mul_right hL3R2).mul_right hL3R4
  have hL4 : Commute (eMat hex u₁ (c • u₂))
      (eMat hex u₂ (b' • y₂) * eMat hex u₁ (a' • z₃) * eMat hex u₁ (c' • u₂)) :=
    (hL4R1.mul_right hL4R2).mul_right hL4R4
  exact (hL1.mul_left (hL2.mul_left hL3)).mul_left hL4

theorem exists_heis_pair_omega (hQ : (polarBilin Q).Nondegenerate)
    (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)
    (hd : 7 ≤ d) {u₁ u₂ z₁ z₂ : Fin d → K} (hu₁0 : u₁ ≠ 0) (hu₁ : Q u₁ = 0) (hu₂ : Q u₂ = 0)
    (h12 : polar Q u₁ u₂ = 0) (hu₂s : u₂ ∉ Submodule.span K {u₁})
    (hz₁ : polar Q u₁ z₁ = 0) (hz₁' : polar Q u₂ z₁ = 0) (hz₂ : polar Q u₁ z₂ = 0)
    (hz₂' : polar Q u₂ z₂ = 0) (hz : polar Q z₁ z₂ = 0)
    (hz₁s : z₁ ∉ Submodule.span K {u₁, u₂}) :
    ∃ ι₁ ι₂ : Heis K →* matrixProjectiveDerived Q, Function.Injective ι₁ ∧
      Function.Injective ι₂ ∧ (∀ a b, Commute (ι₁ a) (ι₂ b)) ∧
      (∀ c, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩) ∧
      ι₁ ⟨1, 0, 0⟩ = matrixProjectiveProjection Q (eMat hex u₁ z₁ * eMat hex u₂ z₂) := by
  classical
  obtain ⟨y₁, hy₁, hy₂, hzy⟩ := exists_polar_eq_one_of_notMem_span (Q := Q) hQ hz₁s
  obtain ⟨z₃, y₂, h₃₁, h₃₂, hy₂₁, hy₂₂, h₃y, h₂₃, hy₁₃, h₁y⟩ :=
    exists_heis_partner (z₂ := z₂) hQ hd hy₁ hy₂ hzy
  obtain ⟨ι₁, hι₁, hι₁x⟩ :=
    exists_heis_omega_of hQ hex hu₁0 hu₁ hu₂ h12 hu₂s hz₁ hz₁' hz₂ hz₂' hz hy₁ hy₂ hzy
  obtain ⟨ι₂, hι₂, hι₂x⟩ :=
    exists_heis_omega_of (z₁ := z₃) (z₂ := 0) (y := y₂) hQ hex hu₁0 hu₁ hu₂ h12 hu₂s h₃₁ h₃₂
      (polar_zero_right Q u₁) (polar_zero_right Q u₂) (polar_zero_right Q z₃) hy₂₁ hy₂₂ h₃y
  refine ⟨ι₁, ι₂, hι₁, hι₂, ?_, ?_, ?_⟩
  · intro a b
    rw [hι₁x a, hι₂x b]
    simp only [smul_zero, eMat_zero, mul_one]
    exact Commute.map
      (eMat_heis_pair_commute hex hu₁ hu₂ h12 hz₁ hz₁' hz₂ hz₂' h₃₁ h₃₂ hy₁ hy₂ hy₂₁ hy₂₂
        h₁y hy₁₃ h₂₃ a.a a.b a.c b.a b.b b.c) (matrixProjectiveProjection Q)
  · intro c
    rw [hι₁x, hι₂x]
    simp only [zero_smul, smul_zero, eMat_zero, one_mul]
  · rw [hι₁x]
    simp only [zero_smul, one_smul, eMat_zero, one_mul, mul_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

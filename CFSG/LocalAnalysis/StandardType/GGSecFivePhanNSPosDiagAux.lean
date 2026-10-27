module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRank
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSCornerDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggNSPosPE_isUnitaryMat_mul {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {g₁ g₂ : GL (Fin n) K}
    (h₁ : ggIsUnitaryMat (p := 2) (f := f) g₁) (h₂ : ggIsUnitaryMat (p := 2) (f := f) g₂) :
    ggIsUnitaryMat (p := 2) (f := f) (g₁ * g₂) := by
  unfold ggIsUnitaryMat at h₁ h₂ ⊢
  rw [Units.val_mul, conjTr_mul]
  calc conjTr (unitaryInvolution K 2 f) (g₂ : Matrix (Fin n) (Fin n) K) *
        conjTr (unitaryInvolution K 2 f) (g₁ : Matrix (Fin n) (Fin n) K) *
        ((g₁ : Matrix (Fin n) (Fin n) K) * (g₂ : Matrix (Fin n) (Fin n) K))
      = conjTr (unitaryInvolution K 2 f) (g₂ : Matrix (Fin n) (Fin n) K) *
        (conjTr (unitaryInvolution K 2 f) (g₁ : Matrix (Fin n) (Fin n) K) *
          (g₁ : Matrix (Fin n) (Fin n) K)) * (g₂ : Matrix (Fin n) (Fin n) K) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h₁, Matrix.mul_one, h₂]

theorem ggNSPosPE_conj_induces {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f n : ℕ} {ψ : Su K 2 f n →* G} {c : Su K 2 f n} {b : G} {g : GL (Fin n) K}
    (hg : GGInducesUnitary (p := 2) (f := f) ψ b g) :
    GGInducesUnitary (p := 2) (f := f) (ψ.comp (MulAut.conj c).toMonoidHom) b
      ((c : GL (Fin n) K)⁻¹ * g * (c : GL (Fin n) K)) := by
  obtain ⟨hu, hact⟩ := hg
  have hc : ggIsUnitaryMat (p := 2) (f := f) (c : GL (Fin n) K) := c.2.2
  have hci : ggIsUnitaryMat (p := 2) (f := f) ((c : GL (Fin n) K)⁻¹) := (c⁻¹).2.2
  refine ⟨ggNSPosPE_isUnitaryMat_mul (ggNSPosPE_isUnitaryMat_mul hci hu) hc, ?_⟩
  intro x
  obtain ⟨y', hy'eq, hy'act⟩ := hact (c * x * c⁻¹)
  refine ⟨c⁻¹ * y' * c, ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy'eq]
    group
  · have harg : (c * (c⁻¹ * y' * c) * c⁻¹ : Su K 2 f n) = y' := by group
    change b * ψ (MulAut.conj c x) * b⁻¹ = ψ (MulAut.conj c (c⁻¹ * y' * c))
    rw [MulAut.conj_apply, MulAut.conj_apply, harg]
    exact hy'act

end CFSG.StandardType

end

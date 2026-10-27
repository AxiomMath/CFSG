module

public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
public import CFSG.CGT.T75M.SzLemma
public import CFSG.Models.BenderSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.BenderSuzuki (SzModel)

theorem invAut_inner_of_suzuki_one {X : Type} [Group X] [Finite X]
    {a : ℕ} (ha : 1 ≤ a) (e : X ≃* SzModel a) (σ : MulAut X) (hσ2 : σ * σ = 1) {t : X}
    (ht : orderOf t = 2) (hfix : σ t = t) :
    ∃ s : X, s * s = 1 ∧ s * t = t * s ∧ ∀ z : X, σ z = s * z * s⁻¹ := by
  have hK : CFSG.BenderSuzuki.IsBenderGroup X := CFSG.BenderSuzuki.IsBenderGroup.isSuzuki a ha e
  obtain ⟨b, hb⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover.exists_eq_conj_of_suzuki ha
      (e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a))) σ hσ2
  have hσσ : ∀ g : X, σ (σ g) = g := fun g => congrArg (fun f : MulAut X => f g) hσ2
  have hcc : ∀ g : X, (b * b) * g = g * (b * b) := by
    intro g
    have h1 := hσσ g
    rw [hb, MulAut.conj_apply, MulAut.conj_apply] at h1
    calc (b * b) * g = (b * (b * g * b⁻¹) * b⁻¹) * (b * b) := by group
      _ = g * (b * b) := by rw [h1]
  have hbb : b * b = 1 := by
    have hz : b * b ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hcc g).symm
    rw [CFSG.CGT.T75M.center_eq_bot_of_isBenderGroup hK, Subgroup.mem_bot] at hz
    exact hz
  have hbt : b * t = t * b := by
    have h1 := hfix
    rw [hb, MulAut.conj_apply] at h1
    calc b * t = (b * t * b⁻¹) * b := by group
      _ = t * b := by rw [h1]
  refine ⟨b, hbb, hbt, fun z => ?_⟩
  rw [hb, MulAut.conj_apply]

theorem autDich_sz {L : Type} [Group L] [Finite L] {a : ℕ}
    (ha : 1 ≤ a) (e : L ≃* SzModel a) (σ : MulAut L) (hσ : σ * σ = 1) {ā : L}
    (hā : orderOf ā = 2) (hfix : σ ā = ā) :
    (∃ τ : L, τ * τ = 1 ∧ τ * ā = ā * τ ∧ ∀ z : L, σ z = τ * z * τ⁻¹) ∨
      (∃ t : L, orderOf t = 2 ∧ σ t = t ∧ ¬ Commute ā t) :=
  Or.inl (invAut_inner_of_suzuki_one ha e σ hσ hā hfix)

end CFSG.RankThree.GF2n.Tim77

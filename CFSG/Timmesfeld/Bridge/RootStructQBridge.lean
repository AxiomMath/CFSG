module

public import CFSG.Timmesfeld.Bridge.RootStructQMain
public import CFSG.Timmesfeld.Bridge.RootStructOD
public import CFSG.Timmesfeld.Bridge.RootStructBridge
public import CFSG.Timmesfeld.Bridge.RootSets

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem specialClosure_of_nCoreCommutatorInRoot [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hR : NCoreCommutatorInRoot D) : SpecialClosure D := by
  intro d hd e he h4 b hb
  obtain ⟨hz, hdz, hez, -⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  have h4' : orderOf (e * d) = 4 := by rwa [orderOf_mul_comm_eq]
  have hsq : (e * d) ^ 2 = (d * e) ^ 2 :=
    (mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hd) (hD.mul_self_eq_one he) h4).symm
  have hdN : d ∈ nCore D ((d * e) ^ 2) :=
    mem_nCore_of_collinear hclass hD hz hd hdz (mul_sq_mem_of_orderOf_eq_four hclass hD hd he h4)
  have heQ : e ∈ Moufang.twoCore ((d * e) ^ 2) := by
    have := mul_sq_mem_of_orderOf_eq_four hclass hD he hd h4'
    rw [hsq] at this
    exact mem_twoCore_of_collinear hclass hD hz he hez this
  have hbN : b ∈ nCore D ((d * e) ^ 2) :=
    mem_nCore_of_mem_twoCore hb.1 (mem_twoCore_of_mem_rootSet hclass hD hz he heQ hb)
  have h4b : orderOf (d * b) = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD hd he (mem_rootSet_self hd) hb h4
  have hc := hR _ hz d hdN b hbN
  rw [show d * b * d⁻¹ * b⁻¹ = (d * b) ^ 2 by
    rw [hD.inv_eq hd, hD.inv_eq hb.1, sq, ← mul_assoc]] at hc
  exact mem_rootSet_of_mem_rootGroup hclass hz (hD.sq_mem hd hb.1 h4b) hc

theorem gammaResidualStep_of_nCoreStepLarge (h : NCoreStepLarge) : GammaResidualStep := by
  intro G _ D hH IH hl hc
  have := hH.finite
  have hs := specialClosure_of_nCoreCommutatorInRoot hH.isClass hH.root (h G D hH IH hl hc)
  exact ⟨fun d hd e he h4 b hb f hf hzf _ _ => ((hs d hd e he h4 b hb).2 f hf).2 hzf,
    fun d hd e he h4 b hb f hf hzf _ _ => ((hs d hd e he h4 b hb).2 f hf).2 hzf⟩

theorem nCoreCommutatorInRoot_of_rootClosure [Finite G]
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D) (hc : RootClosure D)
    (hOD : OppositeDetermines D) : NCoreCommutatorInRoot D := fun _ hy _ hg _ hh =>
  commutator_mem_rootGroup_of_mem_nCore hclass hD hc hOD hy hg hh

theorem nCoreStepLarge : NCoreStepLarge := by
  intro G _ D hH _ _ hc
  have := hH.finite
  exact nCoreCommutatorInRoot_of_rootClosure hH.isClass hH.root hc (oppositeDetermines_of_hyp hH)

theorem gammaResidualStep : GammaResidualStep :=
  gammaResidualStep_of_nCoreStepLarge nCoreStepLarge

end CFSG.Timmesfeld.Bridge

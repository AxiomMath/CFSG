module

public import CFSG.LocalAnalysis.StandardType.GGFixSub
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangPow
public import CFSG.HardMathSupport.Lang.E6Descent.FixedE6
import all CFSG.HardMathSupport.Lang.E6Descent.FixedE6
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType.E6FieldFix

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent

variable {K : Type} [Field K]

@[expose] noncomputable def fixE6Equiv
    [Finite K]
    {p : ℕ} (σ : K ≃+* K) (hσp : σ ^ p = 1)
    (hcop : Nat.Coprime p 3) :
    adjointGroup Tag.E6 (fixSubfield σ) ≃*
      ↥(ggFixSub (entrywiseAdjointAut Tag.E6 σ)) :=
  (fixedE6Equiv σ hσp hcop).symm.trans (MulEquiv.subgroupCongr (Subgroup.ext fun _ => Iff.rfl))

private theorem baseChangeGL_fixedFieldImageEquiv_symm
    (σ : K ≃+* K)
    (w : ↥(fixedFieldImage Tag.E6 σ)) :
    baseChangeGL (fixSubfield σ).subtype
      ((((fixedFieldImageEquiv (τ := Tag.E6) σ).symm w :
        adjointGroup Tag.E6 (fixSubfield σ)) :
        ModGL Tag.E6 (fixSubfield σ))) = (w : ModGL Tag.E6 K) :=
  congrArg Subtype.val ((fixedFieldImageEquiv (τ := Tag.E6) σ).apply_symm_apply w)

private theorem baseChangeGL_fixedE6Equiv
    [Finite K]
    {p : ℕ} (σ : K ≃+* K) (hσp : σ ^ p = 1)
    (hcop : Nat.Coprime p 3)
    (z : ↥(CFSG.RankThree.PartOne.CTP.fixedSubgroup
      (entrywiseAdjointAut Tag.E6 σ))) :
    baseChangeGL (fixSubfield σ).subtype
      (((fixedE6Equiv σ hσp hcop z : adjointGroup Tag.E6 (fixSubfield σ)) :
        ModGL Tag.E6 (fixSubfield σ))) = (z : ModGL Tag.E6 K) := by
  unfold fixedE6Equiv
  exact baseChangeGL_fixedFieldImageEquiv_symm σ _

theorem coe_fixE6Equiv
    [Finite K]
    {p : ℕ} (σ : K ≃+* K) (hσp : σ ^ p = 1) (hcop : Nat.Coprime p 3)
    (y : adjointGroup Tag.E6 (fixSubfield σ)) :
    ((((fixE6Equiv σ hσp hcop y : ↥(ggFixSub (entrywiseAdjointAut Tag.E6 σ))) :
      adjointGroup Tag.E6 K) : ModGL Tag.E6 K)) =
        baseChangeGL (fixSubfield σ).subtype (y : ModGL Tag.E6 (fixSubfield σ)) := by
  have key := baseChangeGL_fixedE6Equiv σ hσp hcop ((fixedE6Equiv σ hσp hcop).symm y)
  rw [(fixedE6Equiv σ hσp hcop).apply_symm_apply y] at key
  unfold fixE6Equiv
  exact key.symm

theorem mem_ggFixSub_of_mem_map
    {σ : K ≃+* K} (x : adjointGroup Tag.E6 K)
    (hx : (x : ModGL Tag.E6 K) ∈ (adjointGroup Tag.E6 (fixSubfield σ)).map
      (baseChangeGL (fixSubfield σ).subtype)) :
    x ∈ ggFixSub (entrywiseAdjointAut Tag.E6 σ) := by
  obtain ⟨y, -, hyx⟩ := Subgroup.mem_map.1 hx
  rw [mem_ggFixSub]
  apply Subtype.ext
  rw [coe_entrywiseAdjointAut, units_map_entrywiseHom_eq_baseChangeGL, ← hyx,
    baseChangeGL_baseChangeGL]
  rw [show σ.toRingHom.comp (fixSubfield σ).subtype = (fixSubfield σ).subtype from
    RingHom.ext fun a => a.2]

end CFSG.StandardType.E6FieldFix

end

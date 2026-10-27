module

public import CFSG.Quasithin.Vol2.Asc94.TSCaseII
public import CFSG.CGT.M24S.Main
public import CFSG.Quasithin.Vol2.Asc94.Defs
public import CFSG.Quasithin.Vol2.Asc94.HeNoE16
public import CFSG.Quasithin.Vol2.Ch12Sec2SettingK
public import CFSG.CGT.T75E.Nondegenerate
public import CFSG.CGT.T75JM.M22PresInputs
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
public import CFSG.CGT.Timmesfeld75.Sec4Three
public import CFSG.LargeExtraspecial.DWModelSplit
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Th.Max3.Involutions
public import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.CGT.M24S CFSG.Open CFSG.Blueprint

@[expose] def HeCaseIIK : Prop :=
  L52.F6Model → ∀ (G : Type) [Group G] [Finite G] (z : G) (e : ↥(Cz z) ≃* L52.Hc),
    IsSimpleGroup G → CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → Setting G z e →
    Subgroup.normalizer (tr e L52.U1 : Set G) = Cz z →
    Subgroup.normalizer (tr e L52.U2 : Set G) = Cz z →
    Nonempty (G ≃* NativeSporadic.He)

@[expose] def TrichotomyK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), IsSimpleGroup G →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → orderOf z = 2 →
    Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃*
      ↥(Subgroup.centralizer
        ({CFSG.Quasithin.H13.transvection15} :
          Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))) →
    (∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
      g⁻¹ * z * g ≠ z) →
      LieModel G .PSL 5 2 1 ∨ Nonempty (G ≃* NativeSporadic.M24) ∨
        Nonempty (G ≃* NativeSporadic.He)

theorem trichotomyK_of (hM : CFSG.CGT.T75P.M24SylowInput) (hF6 : L52.F6Model)
    (hHe : HeCaseIIK) : TrichotomyK := by
  intro G _ _ z hsimp hK hord ⟨e⟩ hnw
  have S : Setting G z e := ⟨hord, hnw⟩
  by_cases h : Subgroup.normalizer (tr e L52.U1 : Set G) ≠ Cz z ∨
      Subgroup.normalizer (tr e L52.U2 : Set G) ≠ Cz z
  · rcases caseLM hM S h with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · push Not at h
    exact Or.inr (Or.inr (hHe hF6 G z e hsimp hK S h.1 h.2))

end CFSG.Quasithin.A94

namespace CFSG.Quasithin.A94

theorem asc94K_of_leaves (hT : TrichotomyK) (hHe : HeNoE16) :
    CFSG.Quasithin.H13.Asc94_M24He_L52TypeK := by
  intro G _ _ z hsimp hK hord hcent hcore
  have hi := hT G z hsimp hK hord hcent hcore
  refine ⟨hi, fun hE => ?_⟩
  have hnot : ¬ Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.He) := hHe G hE
  rcases hi with h1 | h2 | h3
  · exact ⟨hnot, Or.inl h1⟩
  · exact ⟨hnot, Or.inr h2⟩
  · exact absurd h3 hnot

theorem asc94K_of_typeSplit (hF6 : L52.F6Model) (hHe : HeCaseIIK) (hOrd : He_order) :
    CFSG.Quasithin.H13.Asc94_M24He_L52TypeK :=
  asc94K_of_leaves (trichotomyK_of CFSG.CGT.M24S.m24SylowInput hF6 hHe) (heNoE16_of_order hOrd)

end CFSG.Quasithin.A94

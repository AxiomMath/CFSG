module

public import CFSG.Holt.SL6.Recognition
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.XFusion
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatT
public import CFSG.Goldschmidt.Final
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.InvolutionFixedCentralSylow
public import CFSG.Holt.CaseTwoBW
public import CFSG.Holt.General.Basic
public import CFSG.Holt.General.ComponentsImage
public import CFSG.Holt.General.OddOrbits
public import CFSG.Holt.OddCoreTwoGroupBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.StandardType.FS81.HoltSimpleControl
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinear
public import CFSG.Mathlib.RingTheory.UnitOrderOf
public import CFSG.RankThree.Holt.Basic
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KLC.LayerData
public import CFSG.RankThree.PartOne.KLCE.EngineGroup
public import CFSG.RankThree.PartOne.MB3.Defs
public import CFSG.RankThree.PartOne.MB3.FieldSetting
public import CFSG.RankThree.PartOne.MB3.Orbit
public import CFSG.RankThree.PartOne.S11d.Facts
public import CFSG.RankThree.PartOne.S11d.FactsNormalizer
public import CFSG.RankThree.PartOne.S12.Sec12Two
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG.StandardType.FrameRoute.FS81 (HoltSimpleControl)

theorem eq_top_of_cubeSetting (hHolt : HoltSimpleControl) {X : Type} [Group X] [Finite X]
    (S : CubeSetting X) (hC : ∀ c : X, c * S.z = S.z * c → c ∈ S.L) : S.L = ⊤ := by
  have hzL : S.z ∈ S.L := (S.eL.symm CFSG.Holt.SL6.stdTransvection).2
  refine CFSG.Holt.SL6.eq_top_of_isConj_transvection_centralizer_le_of_holt hHolt S.eL hzL ?_ ?_ ?_
  · have h : S.eL ⟨S.z, hzL⟩ = CFSG.Holt.SL6.stdTransvection := S.eL.apply_symm_apply _
    rw [h]
  · intro c hc
    exact hC c (Subgroup.mem_centralizer_singleton_iff.1 hc)
  · intro x hx
    have hconj : IsConj S.z (x * S.z * x⁻¹) := isConj_iff.2 ⟨x, rfl⟩
    have h1 : IsTransvec (S.eL ⟨x * S.z * x⁻¹, hx⟩) := isTransvec_eL_of_isConj S hx hconj
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_isTransvec h1)
    refine ⟨(S.eL.symm c : X), (S.eL.symm c).2, ?_⟩
    have h2 : S.eL.symm (c * CFSG.Holt.SL6.stdTransvection * c⁻¹) = ⟨x * S.z * x⁻¹, hx⟩ := by
      rw [hc]
      exact S.eL.symm_apply_apply _
    have h3 := congrArg Subtype.val h2
    simpa [CubeSetting.z, map_mul, map_inv] using h3.symm

end CFSG.StandardType.FF81.CentE6

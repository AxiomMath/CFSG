module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.GroupTheory.RegularRepGF2
public import CFSG.GroupTheory.AlternatingFive.SylowTwo
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44A5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAutSylow
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionPerfect
public import CFSG.LocalAnalysis.OddStandard.Seitz77Setup
public import CFSG.LocalAnalysis.OddStandard.Seitz77Thompson
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveRho
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NormalizerGeometry
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.Code.Weights
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import Certificates.Certificate3086
public import Certificates.Certificate3120

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

theorem four_le_dMinDeg_of_isAlt_five {X : Type} [Group X] (hX : IsAlt X 5) :
    4 ≤ dMinDeg X := by
  obtain ⟨e⟩ := hX
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have : IsSimpleGroup X := e.isSimpleGroup
  have : Nontrivial X := IsSimpleGroup.toNontrivial
  have hX60 : Nat.card X = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  obtain ⟨n, f₀, hf₀⟩ := CFSG.GroupTheory.exists_nontrivial_repr_card X
  refine le_csInf ⟨n, f₀, hf₀⟩ ?_
  rintro d ⟨f, hf⟩
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
    · exact h
    · exact absurd (MonoidHom.ker_eq_top_iff.mp h) hf
  have hdvd : Nat.card X ∣ Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) :=
    Subgroup.card_dvd_of_injective f hinj
  rw [hX60, Matrix.card_GL_field (𝔽 := ZMod 2) d, ZMod.card] at hdvd
  by_contra hlt
  push Not at hlt
  interval_cases d <;> simp [Fin.prod_univ_succ] at hdvd

theorem exists_isPGroup_sup_map_eq_top_of_isAlt_five {X : Type} [Group X] (hX : IsAlt X 5)
    {α : MulAut X} (hα : α ≠ 1) :
    ∃ P : Subgroup X, IsPGroup 2 P ∧ P ⊔ P.map α.toMonoidHom = ⊤ := by
  obtain ⟨e⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α' : MulAut (alternatingGroup (Fin 5)) := MulAut.congr e α with hα'def
  have hα' : α' ≠ 1 := by
    intro h
    apply hα
    apply (MulAut.congr e).injective
    rw [map_one]
    exact h
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 (alternatingGroup (Fin 5))) := inferInstance
  have hQ₀ : normalizer ((Q₀ : Subgroup (alternatingGroup (Fin 5))) :
      Set (alternatingGroup (Fin 5))) ≠ ⊤ := by
    intro h
    have h12 : Nat.card (normalizer ((Q₀ : Subgroup (alternatingGroup (Fin 5))) :
        Set (alternatingGroup (Fin 5)))) = 12 :=
      CFSG.GroupTheory.AlternatingFive.card_normalizer_sylow_two Q₀
    rw [h, Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin] at h12
    norm_num [Nat.factorial] at h12
  have hinj := CFSG.LocalAnalysis.GLTheoremA.I1416Rows.toPermHom_mulAut_injective hQ₀
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 2 (alternatingGroup (Fin 5)), α' • Q ≠ Q := by
    by_contra! h
    apply hα'
    apply hinj
    ext Q
    simp [h Q]
  have hcoe : ((α' • Q : Sylow 2 (alternatingGroup (Fin 5))) :
      Subgroup (alternatingGroup (Fin 5))) = (Q : Subgroup _).map α'.toMonoidHom := by
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have htop : (Q : Subgroup (alternatingGroup (Fin 5))) ⊔ (Q : Subgroup _).map α'.toMonoidHom =
      ⊤ := by
    refine CFSG.OddStandard.Seitz77.a5_eq_top_of_two_sylow
      (CFSG.GroupTheory.AlternatingFive.card_sylow_two_eq Q) ?_ ?_ le_sup_left le_sup_right
    · rw [← hcoe]
      exact CFSG.GroupTheory.AlternatingFive.card_sylow_two_eq _
    · intro h
      apply hQ
      apply Sylow.ext
      rw [hcoe]
      exact h.symm
  refine ⟨(Q : Subgroup _).map e.symm.toMonoidHom, Q.isPGroup'.map _, ?_⟩
  have hcomp : ((Q : Subgroup (alternatingGroup (Fin 5))).map e.symm.toMonoidHom).map
      α.toMonoidHom = ((Q : Subgroup _).map α'.toMonoidHom).map e.symm.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp [α', MulAut.congr_apply]
  rw [hcomp, ← Subgroup.map_sup, htop]
  exact Subgroup.map_top_of_surjective _ e.symm.surjective

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

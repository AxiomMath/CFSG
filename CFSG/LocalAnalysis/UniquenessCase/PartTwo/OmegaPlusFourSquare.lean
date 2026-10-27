module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.UniquenessCase.UC22

theorem isL2_iff_statedClassicalModel {X : Type} [Group X] {a : ℕ} :
    UC22.IsL2 X a ↔ StatedClassicalModel X .PSL 2 2 a :=
  CFSG.Blueprint.LieModel.classical_iff (by decide)

noncomputable def statedProjStatedSLTwoEquiv (K : Type) [Field K] [CharP K 2] :
    StatedProj (StatedSL 2 K) ≃* ↥(StatedSL 2 K) :=
  (QuotientGroup.quotientMulEquivOfEq
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := K))).trans
    QuotientGroup.quotientBot

noncomputable def statedProjStatedOmegaFourEquiv (K : Type) [Field K] [CharP K 2] :
    StatedProj (StatedOmega (StatedQuadPlus 2 K)) ≃* ↥(StatedOmega (StatedQuadPlus 2 K)) := by
  have hv : ∃ v, CFSG.LieType.Universal.Spin.quadPlus 2 K v ≠ 0 := by
    refine ⟨Pi.single (Sum.inl (0 : Fin 2)) 1 + Pi.single (Sum.inr (0 : Fin 2)) 1, ?_⟩
    rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
    simp [Pi.single_apply, Fin.sum_univ_two]
  exact (QuotientGroup.quotientMulEquivOfEq
    (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := CFSG.LieType.Universal.Spin.quadPlus 2 K) (Q₀ := StatedQuadPlus 2 K)
      (CFSG.LieType.Universal.Spin.coe_quadPlus 2 K) hv)).trans
    QuotientGroup.quotientBot

theorem nonempty_statedOmegaFour_mulEquiv_prod {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) :
    Nonempty (↥(StatedOmega (StatedQuadPlus 2 K)) ≃*
      ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
  obtain ⟨e⟩ := CFSG.Quasithin.G11.P3Ortho.Om4.iso_of_card K h4
  exact ⟨e.trans (MulEquiv.prodCongr (specialLinearGroupEquivStatedSL 2 K)
    (specialLinearGroupEquivStatedSL 2 K))⟩

theorem isL2Square_of_isOmegaPlus {X : Type} [Group X] {a : ℕ} (ha : 2 ≤ a)
    (h : IsOmegaPlus X 4 a) : UC22.IsL2Square X a := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  have h4a : 4 ≤ 2 ^ a := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    exact h4a
  haveI hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  have hadm : StatedLieAdmissible .PSL 2 2 a := by
    refine ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩
    · intro h3
      have h2 := congrArg Prod.snd h3
      omega
    · intro h3
      have h2 := congrArg Prod.snd h3
      omega
  have hSL : UC22.IsL2 ↥(StatedSL 2 K) a := by
    rw [isL2_iff_statedClassicalModel]
    exact ⟨hadm, K, hKf, hKfin, hKcard, ⟨(statedProjStatedSLTwoEquiv K).symm⟩⟩
  obtain ⟨eΩ⟩ := nonempty_statedOmegaFour_mulEquiv_prod (K := K) h4
  have eProj : StatedProj (StatedOmega (StatedQuadPlus 2 K)) ≃*
      ↥(StatedSL 2 K) × ↥(StatedSL 2 K) :=
    (statedProjStatedOmegaFourEquiv K).trans eΩ
  have e' : X ≃* StatedProj (StatedOmega (StatedQuadPlus 2 K)) := e
  exact ⟨↥(StatedSL 2 K), ↥(StatedSL 2 K), inferInstance, inferInstance,
    ⟨e'.trans eProj⟩, hSL, hSL⟩

theorem isOmegaPlus_of_isL2Square {X : Type} [Group X] {a : ℕ} (ha : 2 ≤ a)
    (h : UC22.IsL2Square X a) : IsOmegaPlus X 4 a := by
  obtain ⟨A, B, hAg, hBg, ⟨e⟩, hLA, hLB⟩ := h
  letI := hAg
  letI := hBg
  have hSA : StatedClassicalModel A .PSL 2 2 a :=
    (isL2_iff_statedClassicalModel (X := A) (a := a)).1 hLA
  have hSB : StatedClassicalModel B .PSL 2 2 a :=
    (isL2_iff_statedClassicalModel (X := B) (a := a)).1 hLB
  obtain ⟨eBA⟩ :=
    CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hSB hSA
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eA⟩⟩ := hSA
  letI := hKf
  letI := hKfin
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  haveI hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  obtain ⟨eΩ⟩ := nonempty_statedOmegaFour_mulEquiv_prod (K := K) h4
  have eFull : StatedProj (StatedSL 2 K) × StatedProj (StatedSL 2 K) ≃*
      StatedProj (StatedOmega (StatedQuadPlus 2 K)) :=
    (MulEquiv.prodCongr (statedProjStatedSLTwoEquiv K) (statedProjStatedSLTwoEquiv K)).trans
      (eΩ.symm.trans (statedProjStatedOmegaFourEquiv K).symm)
  have eX : X ≃* StatedProj (StatedSL 2 K) × StatedProj (StatedSL 2 K) :=
    (e.trans (MulEquiv.prodCongr (MulEquiv.refl A) eBA)).trans
      (MulEquiv.prodCongr eA eA)
  refine ⟨by decide, K, hKf, hKfin, hKcard, ?_⟩
  exact ⟨eX.trans eFull⟩

theorem isOmegaPlus_four_iff_isL2Square {X : Type} [Group X] {a : ℕ} (ha : 2 ≤ a) :
    IsOmegaPlus X 4 a ↔ UC22.IsL2Square X a :=
  ⟨isL2Square_of_isOmegaPlus ha, isOmegaPlus_of_isL2Square ha⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.Quasithin.Background.A318PL3Inst
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

theorem ord7Param_U33 : Ord7Param .PSU 3 3 1 := by
  intro R _ _ _hR hmodel
  have hClass : StatedClassicalModel R .PSU 3 3 1 :=
    hmodel.statedClassicalModel_of_ne_zero (by norm_num)
  have hOuter : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer R) ∣ 2 := by
    have h := CFSG.Quasithin.A318P.outer_dvd_unitary (p₀ := 3) (e₀ := 1) hClass
    simpa using h
  have hcard : Nat.card (MulAut R) =
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer R) *
        Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner R) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.ComponentClassification.OuterAutomorphisms.inner R)
  have hInner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner R) ∣
      Nat.card R := by
    show Nat.card (MulAut.conj : R →* MulAut R).range ∣ Nat.card R
    exact Subgroup.card_range_dvd (MulAut.conj : R →* MulAut R)
  have hdvd : Nat.card (MulAut R) ∣ 2 * Nat.card R := by
    rw [hcard]
    exact mul_dvd_mul hOuter hInner
  have hR0 : Nat.card R ≠ 0 := (Nat.card_pos (α := R)).ne'
  have hAut0 : Nat.card (MulAut R) ≠ 0 := (Nat.card_pos (α := MulAut R)).ne'
  have h2R0 : 2 * Nat.card R ≠ 0 := mul_ne_zero (by norm_num) hR0
  calc
    (Nat.card (MulAut R)).factorization 7
        ≤ (2 * Nat.card R).factorization 7 :=
          (Nat.factorization_le_iff_dvd hAut0 h2R0).mpr hdvd 7
    _ = (2 : ℕ).factorization 7 + (Nat.card R).factorization 7 := by
          rw [Nat.factorization_mul (by norm_num : (2 : ℕ) ≠ 0) hR0, Finsupp.add_apply]
    _ = (Nat.card R).factorization 7 := by
          rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 2), zero_add]

end CFSG.StandardType.SporadicShape

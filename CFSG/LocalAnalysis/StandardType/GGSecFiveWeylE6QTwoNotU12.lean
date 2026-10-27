module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLiftLocal
public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.GF2Type.ModelPSU
public import CFSG.LargeExtraspecial.OutSixUnitary
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

theorem E6QTwo.nine_le_twoLocalPrimeRank_of_mulEquiv_psu12 {G : Type} [Group G] [Finite G]
    (e : G ≃* timmesfeldPSU 12) : 9 ≤ twoLocalPrimeRank 3 G := by
  have hloc : 9 ≤ CFSG.Assembly.RankThreeEven.localRank 3
      (StatedProj (StatedSU 12 2 (GaloisField 2 2))) :=
    CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus
      (K := GaloisField 2 2) (p := 2) (f := 1) (r := 3) (k := 8) (n := 12)
      CFSG.LargeExtraspecial.S14.unitaryFieldData_two_one Nat.prime_three
      (by norm_num) (by norm_num) (Or.inl (by norm_num))
  obtain ⟨U, hU2, hU0, E, hEN, hEel, hEcard⟩ :=
    CFSG.RankThree.PartOne.exists_elemAbelian_of_le_localRank (p := 3) (k := 9)
      Nat.prime_three (by norm_num) hloc
  let ee : G ≃* StatedProj (StatedSU 12 2 (GaloisField 2 2)) :=
    e.trans (CFSG.GF2Type.timmesfeldPSUEquivStatedProj 12)
  exact CFSG.LocalAnalysis.GLTheoremA.le_twoLocalPrimeRank_of_surjective
    (φ := ee.toMonoidHom) ee.surjective Nat.prime_three (by norm_num)
    (by
      rw [MonoidHom.ker_eq_bot ee.toMonoidHom ee.injective, Subgroup.card_bot]
      norm_num)
    hU0 hU2 ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).1 hEel)
    hEcard hEN

theorem GGSecFiveE6QTwoCfg.not_nonempty_mulEquiv_psu12
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J) (hBs : Nat.card Bs ≤ 3 ^ 8) :
    ¬ Nonempty (G ≃* timmesfeldPSU 12) := by
  rintro ⟨e⟩
  obtain ⟨𝒦, hRoute, -⟩ := hC
  have hcfg : GGConfig 3 B Bs x L D J := hRoute.1.1
  have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G :=
    hcfg.1.2.2.2.2.2.2.1.1.2.1
  have hBle : B ≤ Bs := hcfg.2.1.1
  have h9 : 9 ≤ twoLocalPrimeRank 3 G :=
    E6QTwo.nine_le_twoLocalPrimeRank_of_mulEquiv_psu12 e
  have htr : LargeEvenTwoLocalRank 3 G = twoLocalPrimeRank 3 G := rfl
  have hle : 3 ^ 9 ≤ 3 ^ 8 := by
    calc 3 ^ 9 ≤ 3 ^ twoLocalPrimeRank 3 G := Nat.pow_le_pow_right (by norm_num) h9
      _ = 3 ^ LargeEvenTwoLocalRank 3 G := by rw [htr]
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le hBle
      _ ≤ 3 ^ 8 := hBs
  norm_num at hle

end CFSG.StandardType

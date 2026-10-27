module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedClDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430LieOutA6
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1425ON
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.LayerTransport
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Glue
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalModel
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcF4O2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1429Red
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05I1416Spor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cClause
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015U6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YCase2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CrossCharOdd
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop115b
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs
public import Certificates.Certificate8007
public import Certificates.Certificate8008

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem ggA6_not_shape_of_a6 (J J' : Type) [Group J] [Group J']
    (hA6 : Nonempty (J ≃* alternatingGroup (Fin 6)))
    (hJJ : Nonempty (J ⧸ Subgroup.center J ≃* J' ⧸ Subgroup.center J')) :
    ¬ GGA6CharTwoLie J' := by
  rintro ⟨t', k, e, hm⟩
  obtain ⟨eJ⟩ := hA6
  obtain ⟨eJJ⟩ := hJJ
  have hA6c : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
  have hmap : (Subgroup.center J).map (eJ : J →* alternatingGroup (Fin 6)) =
      Subgroup.center (alternatingGroup (Fin 6)) := Subgroup.map_center_eq eJ
  rw [hA6c] at hmap
  have hZJ : Subgroup.center J = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center J) eJ.injective).mp hmap
  have e1 : J ⧸ Subgroup.center J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot
  have eA : J' ⧸ Subgroup.center J' ≃* alternatingGroup (Fin 6) :=
    eJJ.symm.trans (e1.trans eJ)
  exact CFSG.LocalAnalysis.GLTheoremA.H1431c.not_lieModel_two_of_isA6
    (CFSG.LocalAnalysis.GLTheoremA.S8.L84.catalogIs_isA6_of_equiv eA) hm

end CFSG.StandardType.A6Red

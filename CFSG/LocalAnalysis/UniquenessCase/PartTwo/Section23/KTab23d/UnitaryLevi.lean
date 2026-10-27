module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.H13.U4ParPoint
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.UnitaryTransport
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Bar2Map
import CFSG.Quasithin.H13.U4ParPointQuot
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.GroupTheory.PCore.Transport
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.B1More8
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B1MoreSeven
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.B6Offenders
import CFSG.Quasithin.Background.E2Hyp
import CFSG.Quasithin.Background.E2SolvTwo
import CFSG.Quasithin.Background.F2Equiv
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.H13.StatementsL3
import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs
import CFSG.Quasithin.Vol2.Ch5StatementsB
import CFSG.Quasithin.Vol2.Ch5StatementsDS
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
import CFSG.Walter.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.H13.U4Par
open CFSG.ClassicalGroups.UnitaryFlag

private theorem nonempty_bar2_hinf_parP_sl2_Q07 {a : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 a K) (ha : 2 ≤ a) :
    Nonempty (Bar2 (Hinf (parP h)) ≃* Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
  rw [show Hinf (parP h) = CFSG.Quasithin.perfectCore (parP h) from
    (CFSG.Quasithin.perfectCore_eq_map_perfectResidual (parP h)).symm]
  exact ⟨modO2PerfectCoreParPEquivSL2 h ha⟩

theorem nonempty_bar2_hinf_lineStab_statedSU_four {a : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 a K) (ha : 2 ≤ a) :
    Nonempty (Bar2 (Hinf (lineStab (StatedSU 4 (2 ^ a) K)
      (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K))) ≃*
        Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
  obtain ⟨R, hR, he⟩ := exists_isHypTransport_four h
  haveI : Finite (hypSU h 2 0) := CFSG.ClassicalGroups.UnitaryFlag.finite_hypSU h
  haveI : Finite (unitarySU 2 a K (2 * 2 + 0)) := inferInstance
  obtain ⟨e⟩ := nonempty_bar2_hinf_map (hypTransport h hR) (parP h)
  rw [map_parP_hypTransport_eq_lineStab h hR he] at e
  obtain ⟨f⟩ := nonempty_bar2_hinf_parP_sl2_Q07 h ha
  exact ⟨e.symm.trans f⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

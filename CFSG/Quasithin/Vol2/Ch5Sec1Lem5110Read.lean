module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110One
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5110Two
public import CFSG.Quasithin.H13.VolIA36
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCore
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellThompson
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecAFacts
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.RankThree.PerfectCover.HopfCentralCoversLift

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem stmt5_1_10_E22_of
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) (h36 : A36ForSQTK) :
    Stmt5_1_10_E22 := by
  intro G _ _ T M L H B D K n k hyp hN hKc hHK hq hcases
  have s : Set510 G T M L H B D K n k := ⟨hyp, hN, hKc, hHK, hq, hcases⟩
  refine ⟨s.oTwoUpper_eq, ?_⟩
  by_cases hT : T ≤ Subgroup.normalizer (K : Set G)
  · obtain ⟨hB, hc⟩ := s.concl_two hGA h36 hT
    exact ⟨hB, Or.inr hc⟩
  · obtain ⟨hB, hlt, htype⟩ := s.concl_one hT
    exact ⟨hB, Or.inl ⟨hlt, htype⟩⟩

theorem stmt5_1_10_of_inputs
    (h331 : Stmt3_3_1) (hE22 : E2.E22StatementC)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) : Stmt5_1_10 :=
  stmt5_1_10_of h331 hE22 (stmt5_1_10_E22_of hGA VolI.a36ForSQTK_holds)

end CFSG.Quasithin.H13

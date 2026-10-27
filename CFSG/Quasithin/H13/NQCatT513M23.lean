module

public import CFSG.Quasithin.H13.NQCatT513Hall
public import CFSG.Quasithin.H13.NQCatA314M23
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionConjugation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.H13.A7Nat1238YCases
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecBL2ODone
public import CFSG.Quasithin.Vol2.Ch11SecBL2UOver
public import CFSG.Quasithin.Vol2.Ch11SecBTCStar
public import CFSG.Quasithin.Vol2.Ch11SecCFacts
public import CFSG.Quasithin.Vol2.Ch11SecCFacts2
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym4
public import CFSG.Quasithin.Vol2.Ch11SecSSym5
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112M23
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Type
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem512
public import CFSG.Quasithin.Vol2.KGNatCoord
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1
public import CFSG.Walter.JRFacts
public import CFSG.Walter.PSL2Facts

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.A312M23
open CFSG.Quasithin.H.MathieuLat

theorem cycOddPerm_m23Grp :
    CycOddPerm ↥CFSG.Blueprint.NativeSporadic.M23 fun _ => False := by
  refine cycOddPerm_of_overgroups m23_S_sylow fun Z hZ m hm => ?_
  obtain ⟨j, hj, rfl⟩ := m23_complete Z hZ
  have hS : Nat.card ↥m23Ctx.S = 128 :=
    card_of_isSylowTwoOf_top m23_S_sylow (a := 7) (m := 79695)
      (by rw [CFSG.Sporadic.Schreier.m23_card]; norm_num) (by decide)
  rw [A314D.card_memberOrTop hj, hS] at hm
  interval_cases j <;> simp at hm <;> omega

theorem cycOddPerm_m23 :
    CycOddPerm (CFSG.Blueprint.NativeSporadic.Carrier .M23) fun _ => False :=
  cycOddPerm_m23Grp

end CFSG.Quasithin.H13.NQCat.T513P

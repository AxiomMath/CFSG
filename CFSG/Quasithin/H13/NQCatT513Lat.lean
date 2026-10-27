module

public import CFSG.Quasithin.H13.NQCatT513Hall
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionConjugation
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A312SporGen
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.H13.A7Nat1238YCases
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
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
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1
public import CFSG.Walter.JRFacts
public import CFSG.Walter.PSL2Facts

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

theorem index_of_list {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ} {Y : ℕ → Subgroup Γ}
    {L : Array ℕ} (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hcard : ∀ j < L.size, Nat.card ↥(Y j) = L[j]! * Nat.card ↥S) {Z : Subgroup Γ} (hZ : S ≤ Z)
    {m : ℕ} (hm : Nat.card ↥Z = m * Nat.card ↥S) :
    (∃ j < L.size, m = L[j]!) ∨ Nat.card Γ = m * Nat.card ↥S := by
  obtain ⟨j, -, rfl⟩ := hall Z hZ
  have hpos : 0 < Nat.card ↥S := Nat.card_pos
  by_cases hjL : j < L.size
  · rw [memberOrTop, ite_eq_left hjL, hcard j hjL] at hm
    exact Or.inl ⟨j, hjL, (Nat.eq_of_mul_eq_mul_right hpos hm).symm⟩
  · rw [memberOrTop, ite_eq_right hjL, Subgroup.card_top] at hm
    exact Or.inr hm

theorem cycOddPerm_of_list {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ}
    (hS : IsSylowTwoOf S ⊤) {Y : ℕ → Subgroup Γ} {L : Array ℕ}
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hcard : ∀ j < L.size, Nat.card ↥(Y j) = L[j]! * Nat.card ↥S)
    (hL : ∀ j < L.size, L[j]! = 1 ∨ 3 ∣ L[j]!) {N : ℕ} (hΓ : Nat.card Γ = N * Nat.card ↥S)
    (hN : 3 ∣ N) : CycOddPerm Γ fun _ => False := by
  refine cycOddPerm_of_overgroups hS fun Z hZ m hm => ?_
  rcases index_of_list hall hcard hZ hm with ⟨j, hj, rfl⟩ | h
  · exact hL j hj
  · have hpos : 0 < Nat.card ↥S := Nat.card_pos
    rw [hΓ] at h
    rw [← Nat.eq_of_mul_eq_mul_right hpos h]
    exact Or.inr hN

end CFSG.Quasithin.H13.NQCat.T513P

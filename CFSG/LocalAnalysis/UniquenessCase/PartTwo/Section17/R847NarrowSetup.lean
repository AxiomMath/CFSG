module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R847Narrow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R847E3L34Normal
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847ThinNe3Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3L3
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3CZHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847FieldsG4
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.R847SU3RankTwo
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (Standing Setup)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedSolvableQ StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def R847E3ThinRes (D : Data G) : Prop :=
  D.sig = {3} → 2 ≤ CFSG.Open.pRank 3 (barPreimage D.M (centE D.M)) →
    ∀ Y ∈ calC D.M, (Y.subgroupOf D.M).Normal → F08.Thin8 Y → ¬ IsL3 (Bar2 Y) 1 →
      ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → 5 ≤ q → Nat.card X = q →
        pCoreOf 2 D.M ⊓ centralizer (X : Set G) = ⊥ →
          normalizer (X : Set G) ≤ D.M ∨ E9O2Normal D.M

theorem r847E3ThinRes_dataOfSetup (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hK3 : StronglyEmbeddedThree) (hS : Standing G) (S : Setup G) :
    R847E3ThinRes (dataOfSetup hS S) := by
  intro hsig _ Y hY hYN hthin _ X hXY q hq hq5 hXc _
  exact normalizer_le_or_e9O2Normal_of_thin_three hThin hCyc hG3 hRee hK3 hS S
    (by rw [hsig]; exact Set.mem_singleton 3) hY hYN hthin hq hq5 hXY hXc

theorem r847Thin17_dataOfSetup
    (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ) (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hSQ : StronglyEmbeddedSolvableQ) (hK3 : StronglyEmbeddedThree)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hS : Standing G) (S : Setup G) (hres : R847E3ThinRes (dataOfSetup hS S)) :
    R847Thin17 (dataOfSetup hS S) := by
  intro Y hY hthin X hXY q hq hq2 hXq p hp
  by_cases hYN : (Y.subgroupOf (dataOfSetup hS S).M).Normal
  swap
  · exact Or.inl (r847E3ThinNN_dataOfSetup hSE hSEZ hThin hSQ hK3 hG3 hRee hS S Y hY hYN hthin
      X hXY q hq hq2 hXq p hp)
  by_cases hp' : ∃ p' ∈ (dataOfSetup hS S).sig, p' ≠ 3
  · obtain ⟨p', hp'σ, hp'3⟩ := hp'
    exact Or.inl (r847ThinNe3_dataOfSetup hSE hSEZ hThin hCyc hSQ hK3 hG3 hRee hS S Y hY hthin
      X hXY q hq hq2 hXq p' hp'σ hp'3)
  push Not at hp'
  obtain rfl : p = 3 := hp' p hp
  have hsig : (dataOfSetup hS S).sig = {3} := Set.eq_singleton_iff_unique_mem.2 ⟨hp, hp'⟩
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXq
    exact hq.one_lt.ne hXq
  by_cases hq3 : q = 3
  · subst hq3
    exact Or.inl (uc22ine229_normalizer_le_of_mem_sig (UC6S846.sigmaStd_dataOfSetup hS S) hY hp
      hXY hX1 (IsPGroup.of_card (n := 1) (by rw [hXq, pow_one])))
  have hq5 : 5 ≤ q := hq.five_le_of_ne_two_of_ne_three hq2 hq3
  by_cases hL3 : IsL3 (Bar2 Y) 1
  · exact Or.inl (r847E3L3_dataOfSetup hSE hSEZ hThin hCyc hG3 hRee hK3 hS S Y hY hYN hL3 X hXY
      (by rw [hXq]; exact hq) (by rw [hXq]; exact hq2))
  by_cases hCZ : pCoreOf 2 (dataOfSetup hS S).M ⊓ centralizer (X : Set G) = ⊥
  swap
  · exact Or.inl (r847ThinCZ_dataOfSetup_holds hSE hSEZ hThin hCyc hSQ hK3 hG3 hRee hS S Y hY
      hthin X hXY (by rw [hXq]; exact hq) (by rw [hXq]; exact hq2) hCZ)
  by_cases hC : 2 ≤ CFSG.Open.pRank 3
      (barPreimage (dataOfSetup hS S).M (centE (dataOfSetup hS S).M))
  swap
  · rcases r847E3Thin_dataOfSetup hSE hSEZ hThin hCyc hG3 hRee hK3 hS S Y hY hYN hthin X hXY q
      hq hq2 hXq 3 hp with h | ⟨-, h⟩
    · exact Or.inl h
    · exact absurd h hC
  rcases hres hsig hC Y hY hYN hthin hL3 X hXY q hq hq5 hXq hCZ with h | h
  · exact Or.inl h
  · exact Or.inr ⟨rfl, h⟩

theorem r847Sec17_dataOfSetup
    (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ) (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hSQ : StronglyEmbeddedSolvableQ) (hK3 : StronglyEmbeddedThree)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hgr : GriessAllModelsStatement) (hC : uc22pwCartanSU3) (hT : uc22pwTorusSU3)
    (hS : Standing G) (S : Setup G) (h846 : F08.R846 (dataOfSetup hS S))
    (hres : R847E3ThinRes (dataOfSetup hS S)) : R847Sec17 (dataOfSetup hS S) :=
  ⟨r847Thin17_dataOfSetup hSE hSEZ hThin hCyc hSQ hK3 hG3 hRee hS S hres,
    r847SU3G4_dataOfSetup hSE hSEZ hG3 hRee hK3 hgr hC hT hS S h846
      (r847E3SU3G4Res_dataOfSetup_of_rankTwo hG3 hRee hK3 hgr hT hC hS S
        (r847E3SU3G4RankTwo_dataOfSetup hS S))⟩

theorem r847Sec17_of_r847G4 {D : Data G} (h : R847G4 D) : R847Sec17 D :=
  ⟨r847Thin17_of_r847G4 h, UC22.r847SU3G4_of_r847G4 h⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

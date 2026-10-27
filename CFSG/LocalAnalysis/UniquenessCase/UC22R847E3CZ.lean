module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NN
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3L3
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedSolvableQ StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]

@[expose] def R847E3CZRes (D : Data G) : Prop :=
  D.sig = {3} → 2 ≤ CFSG.Open.pRank 3 (barPreimage D.M (centE D.M)) →
    ∀ Y ∈ calC D.M, (Y.subgroupOf D.M).Normal → F08.Thin8 Y → ¬ IsL3 (Bar2 Y) 1 →
      ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → 5 ≤ q → Nat.card X = q →
        CFSG.Open.pCoreOf 2 D.M ⊓ centralizer (X : Set G) ≠ ⊥ → normalizer (X : Set G) ≤ D.M

theorem r847ThinCZ_dataOfSetup
    (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ) (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hSQ : StronglyEmbeddedSolvableQ) (hK3 : StronglyEmbeddedThree)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hS : Standing G) (S : Setup G) (hres : R847E3CZRes (dataOfSetup hS S)) :
    ∀ Y ∈ calC (dataOfSetup hS S).M, F08.Thin8 Y → ∀ X : Subgroup G, X ≤ Y →
      (Nat.card X).Prime → Nat.card X ≠ 2 →
      CFSG.Open.pCoreOf 2 (dataOfSetup hS S).M ⊓ centralizer (X : Set G) ≠ ⊥ →
      normalizer (X : Set G) ≤ (dataOfSetup hS S).M := by
  intro Y hY hthin X hXY hXp hX2 hCZ
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  by_cases hYN : (Y.subgroupOf (dataOfSetup hS S).M).Normal
  · by_cases hp : ∃ p ∈ (dataOfSetup hS S).sig, p ≠ 3
    · obtain ⟨p, hp, hp3⟩ := hp
      rcases r847E3Thin_dataOfSetup hSE hSEZ hThin hCyc hG3 hRee hK3 hS S Y hY hYN hthin X hXY
        _ hXp hX2 rfl p hp with h | ⟨h3, -⟩
      · exact h
      · exact absurd h3 hp3
    push Not at hp
    obtain ⟨p, hp0⟩ := hSg.nonempty
    obtain rfl := hp p hp0
    have hsig : (dataOfSetup hS S).sig = {3} := Set.eq_singleton_iff_unique_mem.2 ⟨hp0, hp⟩
    by_cases hL3 : IsL3 (Bar2 Y) 1
    · exact r847E3L3_dataOfSetup hSE hSEZ hThin hCyc hG3 hRee hK3 hS S Y hY hYN hL3 X hXY hXp hX2
    rcases eq_or_ne (Nat.card X) 3 with hX3 | hX3
    · refine uc22ine229_normalizer_le_of_mem_sig hSg hY hp0 hXY ?_
        (IsPGroup.of_card (n := 1) (by rw [hX3, pow_one]))
      intro h
      rw [h, Subgroup.card_bot] at hX3
      omega
    rcases r847E3Thin_dataOfSetup hSE hSEZ hThin hCyc hG3 hRee hK3 hS S Y hY hYN hthin X hXY
      _ hXp hX2 rfl 3 hp0 with h | ⟨-, h2⟩
    · exact h
    · exact hres hsig h2 Y hY hYN hthin hL3 X hXY _ hXp
        (hXp.five_le_of_ne_two_of_ne_three hX2 hX3) rfl hCZ
  · obtain ⟨p, hp⟩ := hSg.nonempty
    exact r847E3ThinNN_dataOfSetup hSE hSEZ hThin hSQ hK3 hG3 hRee hS S Y hY hYN hthin X hXY _
      hXp hX2 rfl p hp

end CFSG.LocalAnalysis.UniquenessCase.UC22

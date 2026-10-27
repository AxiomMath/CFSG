module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3SU3
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Dvd
import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]

@[expose] def R847E3SU3G4Res (D : Data G) : Prop :=
  D.sig = {3} → ∀ Y ∈ calC D.M, (Y.subgroupOf D.M).Normal → ∀ n : ℕ, IsSU3 (Bar2 Y) n →
    n % 6 = 3 → ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 2 ^ n - 1 →
      Nat.card X = q → normalizer (X : Set G) ≤ D.M

theorem r847SU3G4_dataOfSetup (hSE : StronglyEmbeddedFive)
    (hSEZ : StronglyEmbeddedFiveZ) (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree)
    (hgr : GriessAllModelsStatement) (hC : uc22pwCartanSU3) (hT : uc22pwTorusSU3)
    (hS : Standing G) (S : Setup G) (h846 : F08.R846 (dataOfSetup hS S))
    (hres : R847E3SU3G4Res (dataOfSetup hS S)) :
    ∀ Y ∈ calC (dataOfSetup hS S).M, (Y.subgroupOf (dataOfSetup hS S).M).Normal →
      ∀ n : ℕ, IsSU3 (Bar2 Y) n → ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → q ≠ 2 →
      q ∣ 2 ^ n - 1 → Nat.card X = q → ∀ p ∈ (dataOfSetup hS S).sig,
      normalizer (X : Set G) ≤ (dataOfSetup hS S).M ∨
        (p = 3 ∧ (n % 6 = 1 ∨ n % 6 = 5) ∧ evenRank G = 3) := by
  intro Y hY hYN n hYn X hXY q hq hq2 hqn hXc p hp
  have hSU := r847E3SU3_dataOfSetup_of_dvd hSE hSEZ hG3 hRee hK3 hgr hC hT hS S h846
    (r847E3Dvd_dataOfSetup hSE hSEZ hgr hS S) Y hY hYN n hYn X hXY q hq hq2 hqn hXc
  rcases hSU p hp with h | ⟨rfl, hn⟩
  · exact Or.inl h
  have h2 := Nat.odd_iff.1 hn
  rcases (by omega : n % 6 = 1 ∨ n % 6 = 3 ∨ n % 6 = 5) with h6 | h6 | h6
  · exact Or.inr ⟨rfl, Or.inl h6, hS.rank⟩
  · refine Or.inl ?_
    by_cases hp' : ∃ p' ∈ (dataOfSetup hS S).sig, p' ≠ 3
    · obtain ⟨p', hp', hp'3⟩ := hp'
      rcases hSU p' hp' with h | ⟨h3, -⟩
      · exact h
      · exact absurd h3 hp'3
    push Not at hp'
    exact hres (Set.eq_singleton_iff_unique_mem.2 ⟨hp, hp'⟩) Y hY hYN n hYn h6 X hXY q hq hq2
      hqn hXc
  · exact Or.inr ⟨rfl, Or.inr h6, hS.rank⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

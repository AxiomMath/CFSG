module

public import CFSG.RankThree.PartTwo.Sec8.Hering88Cases
public import CFSG.RankThree.PartTwo.Sec8.Hering88Swap

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KF88StepDOnOdd
    (P : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → G → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, (x = c ∨ x = b) →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      (∃ (A₀ : Subgroup G) (d' : G) (n' : ℕ), Odd n' ∧ P G Y x A₀ d' n') →
      ∃ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x ∧ Good88 Y x d

theorem KF88StepDOn.odd
    {P : ∀ (G : Type) [Group G] [Finite G], Subgroup G → G → Subgroup G → G → ℕ → Prop}
    (h : KF88StepDOn P) : KF88StepDOnOdd P :=
  fun G _ _ A c L a b X n hp Y hY hIJ x hx hxY ⟨A₀, d', n', _, hP⟩ =>
    h G A c L a b X n hp Y hY hIJ x hx hxY ⟨A₀, d', n', hP⟩

@[expose] def KF88StepDCaseOneOdd : Prop := KF88StepDOnOdd fun G _ _ => Case83One

@[expose] def KF88StepDCaseThreeOdd : Prop := KF88StepDOnOdd fun G _ _ => Case83Three

@[expose] def KF88StepDCaseFourOdd : Prop := KF88StepDOnOdd fun G _ _ => Case83Four

theorem kF88StepDData83_of_casesOdd (h1 : KF88StepDCaseOneOdd) (h2 : KF88StepDOnOdd fun G _ _ =>
    Case83Two)
    (h3 : KF88StepDCaseThreeOdd) (h4 : KF88StepDCaseFourOdd) (h5 : KF88StepDOnOdd fun G _ _ =>
        Case83Five) :
    KF88StepDData83 := by
  intro G _ _ A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', n', hD⟩
  rcases (cases83_iff Y x A₀ d' n').mp hD.cases with hc | hc | hc | hc | hc
  · exact h1 G A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', n', hD.odd, hc⟩
  · exact h2 G A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', n', hD.odd, hc⟩
  · exact h3 G A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', n', hD.odd, hc⟩
  · exact h4 G A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', n', hD.odd, hc⟩
  · exact h5 G A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', n', hD.odd, hc⟩

end CFSG.RankThree.PartTwo.Sec8

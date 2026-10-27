module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusMain
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusRu
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSp4Main
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusU3
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusL4
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.Blueprint CFSG.Assembly.RankThreeEven
open BThreeCensus

theorem threePrimeB3Ru :
    ThreePrimeB3Ru :=
  threePrimeB3_ru

@[expose] def ThreePrimeB3EvenChar46Rest : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    ((∃ n : ℕ, 1 ≤ n ∧ Nonempty (X ≃* projSU 4 2 n)) ∨
      (∃ f : ℕ, ChevalleyExceptionalModel X .G2 2 f ∨
        ChevalleyExceptionalModel X .trialityD4 2 f ∨ ReeTitsModel X .twistedF4 2 f)) →
    ThreePrimeB3 X

theorem threePrimeB3EvenChar46_of_rest
    (h : ThreePrimeB3EvenChar46Rest) : ThreePrimeB3EvenChar46 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro X _ _ hq hX
  rcases hX with ⟨n, hn, ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | hU4⟩ | hexc | ⟨n, hn, K, _, _, hSL⟩
  · exact threePrimeB3_of_mulEquiv e (threePrimeB3_projSL_three_galoisField 2 n (by norm_num))
  · exact threePrimeB3_of_mulEquiv e (threePrimeB3_projSU_three_galoisField (by norm_num) hn)
  · exact threePrimeB3_of_mulEquiv e (threePrimeB3_projSp_two_charTwo hn)
  · exact h X hq (Or.inl ⟨n, hn, hU4⟩)
  · exact h X hq (Or.inr hexc)
  · rcases hSL with ⟨hK, ⟨e⟩⟩ | ⟨hK, ⟨e⟩⟩
    · exact threePrimeB3_of_mulEquiv e (threePrimeB3_statedSL_three_all (by norm_num) hK)
    · exact threePrimeB3_of_mulEquiv e (threePrimeB3_statedSU_three_all (by norm_num) hn hK)

@[expose] def ThreePrimeB3OddChar46Rest : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
      (ChevalleyExceptionalModel X .G2 p 1 ∨ (p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)))) →
    ThreePrimeB3 X

theorem threePrimeB3OddChar46_of_rest
    (h : ThreePrimeB3OddChar46Rest) : ThreePrimeB3OddChar46 := by
  intro X _ _ hq hX
  rcases hX with ⟨p, e, _, hp, he1, -, hSL | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ |
    ⟨p, _, hp, hG2 | ⟨⟨φ⟩⟩ | hU4 | ⟨hp2, ⟨φ⟩⟩⟩
  · have hp3 : p ≠ 3 := by omega
    obtain ⟨K, _, _, ⟨hK, ⟨φ⟩⟩ | ⟨hK, ⟨φ⟩⟩⟩ := hSL
    · exact threePrimeB3_of_mulEquiv φ (threePrimeB3_statedSL_three_all hp3 hK)
    · exact threePrimeB3_of_mulEquiv φ (threePrimeB3_statedSU_three_all hp3 he1 hK)
  · exact threePrimeB3_of_mulEquiv φ (threePrimeB3_projSL_three_galoisField p e (by omega))
  · exact threePrimeB3_of_mulEquiv φ (threePrimeB3_projSU_three_galoisField (by omega) he1)
  · exact h X hq ⟨p, inferInstance, hp, Or.inl hG2⟩
  · exact threePrimeB3_of_mulEquiv φ (threePrimeB3_projSp_two_prime hp)
  · exact h X hq ⟨p, inferInstance, hp, Or.inr hU4⟩
  · exact threePrimeB3_of_mulEquiv φ (threePrimeB3_projSL_four_prime hp2)

@[expose] def ThreePrimeB3Residual46Rest : Prop :=
  ThreePrimeB3OddChar46Rest ∧ ThreePrimeB3EvenChar46Rest

theorem threePrimeB3Residual46_of_rest
    (h : ThreePrimeB3Residual46Rest) : ThreePrimeB3Residual46 :=
  threePrimeB3Residual46_of (threePrimeB3OddChar46_of_rest h.1)
    (threePrimeB3EvenChar46_of_rest h.2) threePrimeB3Ru

end CFSG.RankThree.PartTwo.Sec6

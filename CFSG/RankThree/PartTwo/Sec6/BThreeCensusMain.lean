module

public import CFSG.RankThree.PartTwo.Sec6.BThreeCensus
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSz
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusL2
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.Blueprint CFSG.Assembly.RankThreeEven
open BThreeCensus

@[expose] def ThreePrimeB3OddChar46 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    ((∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
        (Sec4.IsSLThreeEpsAt X (p ^ e) ∨ Nonempty (X ≃* projSL 3 (GaloisField p e)) ∨
          Nonempty (X ≃* projSU 3 p e))) ∨
      (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
        (ChevalleyExceptionalModel X .G2 p 1 ∨
          Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
          (p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)) ∨
          (p % 3 = 2 ∧ Nonempty (X ≃* projSL 4 (GaloisField p 1)))))) →
    ThreePrimeB3 X

@[expose] def ThreePrimeB3EvenChar46 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    ((∃ n : ℕ, 1 ≤ n ∧ (Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨
        Nonempty (X ≃* projSU 3 2 n) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨
        Nonempty (X ≃* projSU 4 2 n))) ∨
      (∃ f : ℕ, ChevalleyExceptionalModel X .G2 2 f ∨
        ChevalleyExceptionalModel X .trialityD4 2 f ∨ ReeTitsModel X .twistedF4 2 f) ∨
      ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsSLThreeEpsAt X (2 ^ n)) →
    ThreePrimeB3 X

@[expose] def ThreePrimeB3Ru : Prop :=
  ThreePrimeB3 (NativeSporadic.Carrier .Ru)

@[expose] def ThreePrimeB3Residual46 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    (((∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
        (Sec4.IsSLThreeEpsAt X (p ^ e) ∨ Nonempty (X ≃* projSL 3 (GaloisField p e)) ∨
          Nonempty (X ≃* projSU 3 p e))) ∨
      (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
        (ChevalleyExceptionalModel X .G2 p 1 ∨
          Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
          (p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)) ∨
          (p % 3 = 2 ∧ Nonempty (X ≃* projSL 4 (GaloisField p 1)))))) ∨
    ((∃ n : ℕ, 1 ≤ n ∧ (Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨
        Nonempty (X ≃* projSU 3 2 n) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨
        Nonempty (X ≃* projSU 4 2 n))) ∨
      (∃ f : ℕ, ChevalleyExceptionalModel X .G2 2 f ∨
        ChevalleyExceptionalModel X .trialityD4 2 f ∨ ReeTitsModel X .twistedF4 2 f) ∨
      ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsSLThreeEpsAt X (2 ^ n)) ∨
    Nonempty (X ≃* NativeSporadic.Carrier .Ru)) →
    ThreePrimeB3 X

theorem threePrimeB3Residual46_of (hodd : ThreePrimeB3OddChar46)
    (heven : ThreePrimeB3EvenChar46) (hRu : ThreePrimeB3Ru) : ThreePrimeB3Residual46 := by
  intro X _ _ hq hX
  rcases hX with h | h | ⟨⟨e⟩⟩
  · exact hodd X hq h
  · exact heven X hq h
  · exact threePrimeB3_of_mulEquiv e hRu

theorem threePrimeB3_of_isList46
    (hres : ThreePrimeB3Residual46) (Q : Type) [Group Q] [Finite Q] (hQ : Sec4.IsList46 Q)
    (hq : IsQuasisimple Q) : ThreePrimeB3 Q := by
  rcases hQ with ⟨p, e, _, -, he, ⟨f⟩⟩ | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact threePrimeB3_of_mulEquiv f (threePrimeB3_projSL_two he)
  · exact hres Q hq (Or.inl (Or.inl h2))
  · exact hres Q hq (Or.inl (Or.inr h3))
  · exact threePrimeB3_four h4
  · rcases h5 with ⟨s, hs, ⟨f⟩⟩ | hcov
    · by_cases hsRu : s = .Ru
      · subst hsRu
        exact hres Q hq (Or.inr (Or.inr ⟨f⟩))
      · exact threePrimeB3_five (Or.inl ⟨s, hs, hsRu, ⟨f⟩⟩)
    · exact threePrimeB3_five (Or.inr hcov)
  · rcases h6 with hC | hSL
    swap
    · exact hres Q hq (Or.inr (Or.inl (Or.inr (Or.inr hSL))))
    unfold Sec4.IsChevTwoRankTwoModel at hC
    rcases hC with ⟨n, hn, ⟨⟨f⟩⟩ | h⟩ | ⟨f, h | h | hSz | h | hT⟩
    · exact threePrimeB3_of_mulEquiv f (threePrimeB3_projSL_two hn)
    · exact hres Q hq (Or.inr (Or.inl (Or.inl ⟨n, hn, h⟩)))
    · exact hres Q hq (Or.inr (Or.inl (Or.inr (Or.inl ⟨f, Or.inl h⟩))))
    · exact hres Q hq (Or.inr (Or.inl (Or.inr (Or.inl ⟨f, Or.inr (Or.inl h)⟩))))
    · exact threePrimeB3_of_suzukiModel hSz
    · exact hres Q hq (Or.inr (Or.inl (Or.inr (Or.inl ⟨f, Or.inr (Or.inr h)⟩))))
    · exact threePrimeB3_tits hT
  · exact threePrimeB3_seven h7
  · exact threePrimeB3_eight h8

theorem bThreePropertyThreePrimeCentral_of_census
    (h46 : Sec4.Item4_6) (hres : ThreePrimeB3Residual46) : BThreePropertyThreePrimeCentral :=
  bThreePropertyThreePrimeCentral_of_threePrimeB3 h46 fun Q _ _ hQ hq =>
    threePrimeB3_of_isList46 hres Q hQ hq

section Items

theorem rank3II_6_5_of_census (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6) (h48 : Sec4.Item4_8)
    (h49 : Sec4.Item4_9) (hGW : GWLBalanceStatement) (hres : ThreePrimeB3Residual46) :
    Item6_5 :=
  rank3II_6_5_of_lBalance h45 h48 h49 hGW (bThreePropertyThreePrimeCentral_of_census h46 hres)

theorem rank3II_6_8_of_census (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6) (h48 : Sec4.Item4_8)
    (h49 : Sec4.Item4_9) (hGW : GWLBalanceStatement) (hres : ThreePrimeB3Residual46)
    (hKf : KFacts.KS6OuterIndex) : Item6_8 :=
  rank3II_6_8_of_lBalance h45 h48 h49 hGW (bThreePropertyThreePrimeCentral_of_census h46 hres)
    hKf

end Items

end CFSG.RankThree.PartTwo.Sec6

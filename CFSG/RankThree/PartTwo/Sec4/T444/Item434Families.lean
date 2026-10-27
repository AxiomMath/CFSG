module

public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex)

@[expose] def IsChevTwoRankTwoLarge (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 4 ≤ n ∧ n ≠ 6 ∧
    (Nonempty (X ≃* projSL 2 (GaloisField 2 n)) ∨ Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSU 3 2 n) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSU 4 2 n))) ∨
  (∃ q : TauCeti.PrimePower, q.p = 2 ∧ 4 ≤ q.exponent ∧ q.exponent ≠ 6 ∧ IsoGTwo X q) ∨
  (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
    4 ≤ q.exponent ∧ q.exponent ≠ 6 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∨
  (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid), 2 ≤ m ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group)) ∨
  (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid), 2 ≤ m ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group))

@[expose] def IsChevTwoRankTwoSmall (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ (n ≤ 3 ∨ n = 6) ∧
    (Nonempty (X ≃* projSL 2 (GaloisField 2 n)) ∨ Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSU 3 2 n) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSU 4 2 n))) ∨
  (∃ q : TauCeti.PrimePower, q.p = 2 ∧ (q.exponent ≤ 3 ∨ q.exponent = 6) ∧ IsoGTwo X q) ∨
  (∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p = 2 ∧
    (q.exponent ≤ 3 ∨ q.exponent = 6) ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∨
  (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.suzuki m).Valid), m ≤ 1 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group)) ∨
  (∃ (m : ℕ) (hm : (TauCeti.LieTypeIndex.reeF4 m).Valid), m ≤ 1 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hm⟩).Group)) ∨
  (∃ ht : TauCeti.LieTypeIndex.tits.Valid,
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group))

theorem isChevTwoRankTwo_cases {X : Type} [Group X] (h : IsChevTwoRankTwo X) :
    IsChevTwoRankTwoLarge X ∨ IsChevTwoRankTwoSmall X := by
  rcases h with ⟨n, hn, h⟩ | ⟨q, hq, h⟩ | ⟨q, hv, hq, h⟩ | ⟨m, hm, h⟩ | ⟨m, hm, h⟩ | ⟨ht, h⟩
  · by_cases h4 : 4 ≤ n ∧ n ≠ 6
    · exact Or.inl (Or.inl ⟨n, h4.1, h4.2, h⟩)
    · exact Or.inr (Or.inl ⟨n, hn, by omega, h⟩)
  · by_cases h4 : 4 ≤ q.exponent ∧ q.exponent ≠ 6
    · exact Or.inl (Or.inr (Or.inl ⟨q, hq, h4.1, h4.2, h⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨q, hq, by omega, h⟩))
  · by_cases h4 : 4 ≤ q.exponent ∧ q.exponent ≠ 6
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨q, hv, hq, h4.1, h4.2, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hv, hq, by omega, h⟩)))
  · rcases le_or_gt 2 m with h2 | h2
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, h2, h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, by omega, h⟩))))
  · rcases le_or_gt 2 m with h2 | h2
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm, h2, h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, by omega, h⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, h⟩)))))

@[expose] def IsLie42Generic (X : Type) [Group X] : Prop :=
  (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧
    Nonempty (X ≃* projSL 2 (GaloisField p e))) ∨
  (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
    (Nonempty (X ≃* projSL 3 (GaloisField p e)) ∨ Nonempty (X ≃* projSU 3 p e))) ∨
  (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
    ((∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ IsoGTwo X q) ∨
      Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
      Nonempty (X ≃* projSL 4 (GaloisField p 1)) ∨ Nonempty (X ≃* projSU 4 p 1))) ∨
  IsChevTwoRankTwoLarge X

@[expose] def IsLie42CharThree (X : Type) [Group X] : Prop :=
  (∃ e : ℕ, 1 ≤ e ∧ Nonempty (X ≃* projSL 2 (GaloisField 3 e))) ∨
  (∃ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group)) ∨
  ((∃ e : ℕ, 1 ≤ e ∧ e ≤ 3 ∧
      (Nonempty (X ≃* projSL 3 (GaloisField 3 e)) ∨ Nonempty (X ≃* projSU 3 3 e))) ∨
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group) ∨
    Nonempty (X ≃* projSL 4 (GaloisField 3 1)) ∨ Nonempty (X ≃* projSU 4 3 1))

@[expose] def IsLie42SmallTwo (X : Type) [Group X] : Prop :=
  IsChevTwoRankTwoSmall X ∨
  (Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSU 5 2 1) ∨
    Nonempty (X ≃* projSL 6 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSU 6 2 1) ∨
    Nonempty (X ≃* projSL 7 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSp 3 (GaloisField 2 1)) ∨
    Nonempty (X ≃* projSp 4 (GaloisField 2 1)) ∨
    Nonempty (X ≃* projOmegaPlus 4 (GaloisField 2 1)) ∨
    (∃ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (X ≃* projOmegaMinus 3 (GaloisField 2 1) b c)) ∨
    Nonempty (X ≃* projSL 4 (GaloisField 2 2)) ∨ Nonempty (X ≃* projSp 3 (GaloisField 2 2)) ∨
    Nonempty (X ≃* projSU 5 2 2) ∨ Nonempty (X ≃* projSU 5 2 3) ∨
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group))

@[expose] def IsAlt42 (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ n ≤ 12 ∧ Nonempty (X ≃* alternatingGroup (Fin n))

@[expose] def IsSpor42 (X : Type) [Group X] : Prop :=
  ∃ s ∈ sporadics42, Nonempty (X ≃* Spor s)

theorem list42_cases {X : Type} [Group X] (h : Census.List42 X) :
    IsLie42Generic X ∨ IsLie42CharThree X ∨ IsLie42SmallTwo X ∨ IsAlt42 X ∨ IsSpor42 X := by
  rcases h with ⟨p, e, hp, hp2, he, h⟩ | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · by_cases hp3 : p = 3
    · subst hp3
      exact Or.inr (Or.inl (Or.inl ⟨e, he, h⟩))
    · have : 3 < p := by
        have := hp.out.two_le
        omega
      exact Or.inl (Or.inl ⟨p, e, hp, this, he, h⟩)
  · exact Or.inl (Or.inr (Or.inl h2))
  · exact Or.inr (Or.inl (Or.inr (Or.inl h3)))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h6)))
  · rcases isChevTwoRankTwo_cases h7 with hl | hs
    · exact Or.inl (Or.inr (Or.inr (Or.inr hl)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl hs)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h8)))
  · exact Or.inr (Or.inl (Or.inr (Or.inr h9)))

end CFSG.RankThree.PartTwo.Sec4

module

public import CFSG.RankThree.PartOne.N143.SecRankHard
public import CFSG.RankThree.PartOne.N143.SectionCover

public section

namespace CFSG.RankThree.PartOne.SRC

open TauCeti CFSG.RankThree.PartOne.N143

theorem noLowTwoRankSectionFor_or {P Q : CFSGIndex → Prop} (hP : NoLowTwoRankSectionFor P)
    (hQ : NoLowTwoRankSectionFor Q) : NoLowTwoRankSectionFor (fun i => P i ∨ Q i) :=
  fun L _ _ hK he H M _ _ hM π hπ hU ⟨i, hi, e⟩ =>
    hi.elim (fun h => hP L hK he H M hM π hπ hU ⟨i, h, e⟩)
      (fun h => hQ L hK he H M hM π hπ hU ⟨i, h, e⟩)

@[expose] def IsHardRankTwoLargeIndex : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => r = 3 ∧ q.p ≠ 2 ∧ 4 ≤ q.exponent
  | .lie ⟨.twistedA r q, _⟩ => r = 3 ∧ q.p ≠ 2 ∧ 4 ≤ q.exponent
  | .lie ⟨.B r q, _⟩ => r = 2 ∧ q.p ≠ 2 ∧ 4 ≤ q.exponent
  | _ => False

@[expose] def IsHardG2LargeIndex : CFSGIndex → Prop
  | .lie ⟨.G2 q, _⟩ => q.p ≠ 2 ∧ 4 ≤ q.exponent
  | _ => False

@[expose] def IsHardG2SmallIndex : CFSGIndex → Prop
  | .lie ⟨.G2 q, _⟩ => q.p ≠ 2 ∧ 2 ≤ q.exponent ∧ q.exponent ≤ 3
  | _ => False

@[expose] def IsHardReeIndex : CFSGIndex → Prop
  | .lie ⟨.reeG2 m, _⟩ => 2 ≤ m
  | _ => False

@[expose] def IsHardD4LargeIndex : CFSGIndex → Prop
  | .lie ⟨.trialityD4 q, _⟩ => q.p ≠ 2 ∧ 2 ≤ q.exponent
  | _ => False

@[expose] def IsHardD4PrimeIndex : CFSGIndex → Prop
  | .lie ⟨.trialityD4 q, _⟩ => q.p ≠ 2 ∧ q.exponent = 1
  | _ => False

theorem isHardExceptionalIndex_split (i : CFSGIndex) (h : IsHardExceptionalIndex i) :
    IsHardG2LargeIndex i ∨ IsHardG2SmallIndex i ∨ IsHardReeIndex i ∨ IsHardD4LargeIndex i ∨
      IsHardD4PrimeIndex i := by
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (h : False).elim
  · exact (h : False).elim
  · cases li <;> first | exact (h : False).elim | skip
    · obtain ⟨h1, h2⟩ := h
      by_cases h4 : 4 ≤ ‹PrimePower›.exponent
      · exact Or.inl ⟨h1, h4⟩
      · exact Or.inr (Or.inl ⟨h1, h2, by omega⟩)
    · by_cases h4 : 2 ≤ ‹PrimePower›.exponent
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, h4⟩)))
      · have := ‹PrimePower›.exponent_pos
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, by omega⟩)))
    · exact Or.inr (Or.inr (Or.inl h))
  · exact (h : False).elim

@[expose] def IsHardRankTwoMidIndex : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => r = 3 ∧ q.p ≠ 2 ∧ 2 ≤ q.exponent ∧ q.card ≠ 9
  | .lie ⟨.twistedA r q, _⟩ => r = 3 ∧ q.p ≠ 2 ∧ 2 ≤ q.exponent ∧ q.card ≠ 9
  | .lie ⟨.B r q, _⟩ => r = 2 ∧ q.p ≠ 2 ∧ 2 ≤ q.exponent ∧ q.card ≠ 9
  | _ => False

@[expose] def IsHardRankTwoNineIndex : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => r = 3 ∧ q.card = 9
  | .lie ⟨.twistedA r q, _⟩ => r = 3 ∧ q.card = 9
  | .lie ⟨.B r q, _⟩ => r = 2 ∧ q.card = 9
  | _ => False

@[expose] def IsHardL4NineIndex : CFSGIndex → Prop
  | .lie ⟨.A r q, _⟩ => r = 3 ∧ q.card = 9
  | _ => False

@[expose] def IsHardU4NineIndex : CFSGIndex → Prop
  | .lie ⟨.twistedA r q, _⟩ => r = 3 ∧ q.card = 9
  | _ => False

@[expose] def IsHardPSp4NineIndex : CFSGIndex → Prop
  | .lie ⟨.B r q, _⟩ => r = 2 ∧ q.card = 9
  | _ => False

@[expose] def IsHardG2MidIndex : CFSGIndex → Prop
  | .lie ⟨.G2 q, _⟩ => q.p ≠ 2 ∧ 2 ≤ q.exponent ∧ q.card ≠ 9
  | _ => False

@[expose] def IsHardG2NineIndex : CFSGIndex → Prop
  | .lie ⟨.G2 q, _⟩ => q.card = 9
  | _ => False

theorem isHardRankTwoNineIndex_split (i : CFSGIndex) (h : IsHardRankTwoNineIndex i) :
    IsHardL4NineIndex i ∨ IsHardU4NineIndex i ∨ IsHardPSp4NineIndex i := by
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (h : False).elim
  · exact (h : False).elim
  · cases li <;> first | exact (h : False).elim | skip
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact (h : False).elim

theorem isHardRankTwoIndex_split_nine (i : CFSGIndex) (h : IsHardRankTwoIndex i) :
    IsHardRankTwoMidIndex i ∨ IsHardRankTwoNineIndex i := by
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (h : False).elim
  · exact (h : False).elim
  · cases li <;> first | exact (h : False).elim | skip
    all_goals
      obtain ⟨h1, h2, h3⟩ := h
      by_cases h9 : ‹PrimePower›.card = 9
      · exact Or.inr ⟨h1, h9⟩
      · exact Or.inl ⟨h1, h2, h3, h9⟩
  · exact (h : False).elim

theorem isHardG2SmallIndex_split_nine (i : CFSGIndex) (h : IsHardG2SmallIndex i) :
    IsHardG2MidIndex i ∨ IsHardG2NineIndex i := by
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (h : False).elim
  · exact (h : False).elim
  · cases li <;> first | exact (h : False).elim | skip
    obtain ⟨h1, h2, -⟩ := h
    by_cases h9 : ‹PrimePower›.card = 9
    · exact Or.inr h9
    · exact Or.inl ⟨h1, h2, h9⟩
  · exact (h : False).elim

end CFSG.RankThree.PartOne.SRC

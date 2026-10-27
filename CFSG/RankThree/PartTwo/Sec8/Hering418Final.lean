module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Seven
public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts
public import CFSG.RankThree.PartTwo.Sec8.Hering418L2

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)

@[expose] def IsList46OneRes (X : Type) [Group X] : Prop :=
  ∃ e : ℕ, 1 ≤ e ∧ 3 ∣ e ∧ Nonempty (X ≃* projSL 2 (GaloisField 3 e))

@[expose] def IsList46SixRes (X : Type) [Group X] : Prop :=
  (∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ (Nonempty (X ≃* projSL 3 (GaloisField 2 k)) ∨
      Nonempty (X ≃* projSU 3 2 k) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 k)) ∨
      Nonempty (X ≃* projSU 4 2 k))) ∨
  (∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      (Nat.card K = 2 ^ k ∧ Nonempty (X ≃* StatedSL 3 K)) ∨
      (Nat.card K = (2 ^ k) ^ 2 ∧ Nonempty (X ≃* StatedSU 3 (2 ^ k) K))) ∨
  (∃ f : ℕ, 3 ∣ f ∧ (Blueprint.ChevalleyExceptionalModel X .G2 2 f ∨
      Blueprint.ReeTitsModel X .twistedF4 2 f)) ∨
  (∃ f : ℕ, Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f)

@[expose] def IsSevenEightRes (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSp 3 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSL 3 (GaloisField 3 2)) ∨
    (Nat.card (Subgroup.center X) ≤ 3 ∧
      (Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
        Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1)))

theorem isList46One_cases {X : Type} [Group X] (h : Sec4.IsList46One X) :
    IsLTwoOddNeThree X ∨ IsLTwoThreeNotDvd X ∨ IsList46OneRes X := by
  obtain ⟨p, e, hpf, hp2, he, hX⟩ := h
  by_cases hp3 : p = 3
  · subst hp3
    by_cases h3 : 3 ∣ e
    · exact Or.inr (Or.inr ⟨e, he, h3, hX⟩)
    · exact Or.inr (Or.inl ⟨e, he, h3, hX⟩)
  · exact Or.inl ⟨p, e, hpf, hp2, hp3, he, hX⟩

section Assembly

theorem kF418ModelOn_one_of_res (hres : KF418ModelOn (fun X _ => IsList46OneRes X)) :
    KF418ModelOn (fun X _ => Sec4.IsList46One X) := by
  intro G _ _ L hL hl
  rcases isList46One_cases hl with h | h | h
  · exact kF418ModelOn_L2 G L hL h
  · exact kF418ModelOn_L2Three G L hL h
  · exact hres G L hL h

theorem kF418ModelOn_sevenEight_of_res (hres : KF418ModelOn (fun X _ => IsSevenEightRes X)) :
    KF418ModelOn (fun X _ => Sec4.IsList46Seven X ∨ Sec4.IsList46Eight X) := by
  intro G _ _ L hL hl
  rcases hl with (hX | hX | hX) | (⟨e, he1, he2, hX | hX⟩ | hX | hX)
  · exact kF418ModelOn_sevenEight G L hL (Or.inl hX)
  · exact hres G L hL (Or.inl hX)
  · exact kF418ModelOn_sevenEight G L hL (Or.inr (Or.inl hX))
  · rcases (by omega : e = 1 ∨ e = 2) with rfl | rfl
    · exact kF418ModelOn_sevenEight G L hL (Or.inr (Or.inr (Or.inl hX)))
    · exact hres G L hL (Or.inr (Or.inl hX))
  · rcases (by omega : e = 1 ∨ e = 2) with rfl | rfl
    · exact kF418ModelOn_sevenEight G L hL (Or.inr (Or.inr (Or.inr (Or.inl hX))))
    · exact kF418ModelOn_sevenEight G L hL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hX)))))
  · exact kF418ModelOn_sevenEight G L hL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hX)))))
  · exact hres G L hL (Or.inr (Or.inr hX))

end Assembly

end CFSG.RankThree.PartTwo.Sec8.Hering418

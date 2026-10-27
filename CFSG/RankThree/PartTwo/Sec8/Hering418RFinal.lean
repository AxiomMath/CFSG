module

public import CFSG.RankThree.PartTwo.Sec8.Hering418RSixG2
public import CFSG.RankThree.PartTwo.Sec8.Hering418RSixF4
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofG2Two
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSU)

@[expose] def IsLThreeSix (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ Nonempty (X ≃* projSL 3 (GaloisField 2 k))

@[expose] def IsUThreeSix (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ Nonempty (X ≃* projSU 3 2 k)

@[expose] def IsUFourSix (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ Nonempty (X ≃* projSU 4 2 k)

@[expose] def IsSLThreeSix (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = 2 ^ k ∧ Nonempty (X ≃* StatedSL 3 K)

@[expose] def IsSUThreeSix (X : Type) [Group X] : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ 3 ∣ k ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
    Nat.card K = (2 ^ k) ^ 2 ∧ Nonempty (X ≃* StatedSU 3 (2 ^ k) K)

@[expose] def IsTrialityD4Six (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f

theorem isList46SixRes_iff {X : Type} [Group X] :
    IsList46SixRes X ↔ IsLThreeSix X ∨ IsUThreeSix X ∨ IsSpFourSix X ∨ IsUFourSix X ∨
      IsSLThreeSix X ∨ IsSUThreeSix X ∨ IsGTwoSix X ∨ IsTwistedFFourSix X ∨
        IsTrialityD4Six X := by
  constructor
  · rintro (⟨k, hk, h3, h | h | h | h⟩ | ⟨k, hk, h3, K, hKf, hKfin, h | h⟩ |
      ⟨f, h3, h | h⟩ | ⟨f, h⟩)
    · exact Or.inl ⟨k, hk, h3, h⟩
    · exact Or.inr (Or.inl ⟨k, hk, h3, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨k, hk, h3, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, h3, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, h3, K, hKf, hKfin, h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, h3, K, hKf, hKfin, h⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h3, h⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, h3, h⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, h⟩)))))))
  · rintro (⟨k, hk, h3, h⟩ | ⟨k, hk, h3, h⟩ | ⟨k, hk, h3, h⟩ | ⟨k, hk, h3, h⟩ |
      ⟨k, hk, h3, K, hKf, hKfin, h⟩ | ⟨k, hk, h3, K, hKf, hKfin, h⟩ | ⟨f, h3, h⟩ | ⟨f, h3, h⟩ |
      ⟨f, h⟩)
    · exact Or.inl ⟨k, hk, h3, Or.inl h⟩
    · exact Or.inl ⟨k, hk, h3, Or.inr (Or.inl h)⟩
    · exact Or.inl ⟨k, hk, h3, Or.inr (Or.inr (Or.inl h))⟩
    · exact Or.inl ⟨k, hk, h3, Or.inr (Or.inr (Or.inr h))⟩
    · exact Or.inr (Or.inl ⟨k, hk, h3, K, hKf, hKfin, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨k, hk, h3, K, hKf, hKfin, Or.inr h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨f, h3, Or.inl h⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨f, h3, Or.inr h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨f, h⟩))

section Full

theorem kF418ModelOn_G2Six : KF418ModelOn (fun X _ => IsGTwoSix X) :=
  kF418ModelOn_G2Six_of_gTwoTwo Sec8.Item86ResProof.kF83GTwoTwo_holds

end Full

end CFSG.RankThree.PartTwo.Sec8.Hering418

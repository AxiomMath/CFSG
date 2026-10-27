module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofChevTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSU projSp)
open Res417Three

namespace Res417Five

@[expose] def K417NoDatumSp4Odd : Prop :=
  ∀ n : ℕ, Odd n → ∀ D : Subgroup (projSp 2 (GaloisField 2 n)),
    ¬ IsDatum417 (projSp 2 (GaloisField 2 n)) D

@[expose] def K417DatumSp4Even : Prop :=
  ∀ n : ℕ, 1 ≤ n → Even n → ∀ D : Subgroup (projSp 2 (GaloisField 2 n)),
    IsDatum417 (projSp 2 (GaloisField 2 n)) D →
      Nat.card D = 9 ∧ Nonempty (autIn ⊤ D ≃* DihedralGroup 4)

@[expose] def K417DatumU4Even : Prop :=
  ∀ n : ℕ, 1 ≤ n → Even n → ∀ D : Subgroup (projSU 4 2 n), IsDatum417 (projSU 4 2 n) D →
    Nat.card D = 9 ∧ Nonempty (autIn ⊤ D ≃* DihedralGroup 4)

@[expose] def K417DatumU4Odd : Prop :=
  ∀ n : ℕ, Odd n → ∀ D : Subgroup (projSU 4 2 n), IsDatum417 (projSU 4 2 n) D →
    Nat.card D = 27 ∧ Nonempty (autIn ⊤ D ≃* Equiv.Perm (Fin 4))

@[expose] def K417NoDatumG2D4Odd : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), Odd f →
    (ChevalleyExceptionalModel X .G2 2 f ∨ ChevalleyExceptionalModel X .trialityD4 2 f) →
      ∀ D : Subgroup X, ¬ IsDatum417 X D

@[expose] def K417DatumG2D4Even : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), Even f →
    (ChevalleyExceptionalModel X .G2 2 f ∨ ChevalleyExceptionalModel X .trialityD4 2 f) →
      ∀ D : Subgroup X, IsDatum417 X D →
        Nat.card D = 9 ∧ Nonempty (autIn ⊤ D ≃* DihedralGroup 6)

@[expose] def K417NoDatumF4 : Prop :=
  ∀ (X : Type) [Group X] (f : ℕ), (ReeTitsModel X .twistedF4 2 f ∨ ReeTitsModel X .Tits 2 f) →
    ∀ D : Subgroup X, ¬ IsDatum417 X D

end Res417Five

open Res417Five

theorem k417DatumChevTwo_of (hSpOdd : K417NoDatumSp4Odd) (hSpEven : K417DatumSp4Even)
    (hUEven : K417DatumU4Even) (hUOdd : K417DatumU4Odd) (hGOdd : K417NoDatumG2D4Odd)
    (hGEven : K417DatumG2D4Even) (hF4 : K417NoDatumF4) : K417DatumChevTwo := by
  refine ⟨fun n hn D hD => ?_, fun n hn D hD => ?_, fun X _ f hX D hD => ?_,
    fun X _ f hX D hD => hF4 X f hX D hD⟩
  · rcases Nat.even_or_odd n with hev | hodd
    · exact ⟨hev, hSpEven n hn hev D hD⟩
    · exact (hSpOdd n hodd D hD).elim
  · rcases Nat.even_or_odd n with hev | hodd
    · exact Or.inl ⟨hev, hUEven n hn hev D hD⟩
    · exact Or.inr ⟨hodd, hUOdd n hodd D hD⟩
  · rcases Nat.even_or_odd f with hev | hodd
    · exact ⟨hev, hGEven X f hev hX D hD⟩
    · exact (hGOdd X f hodd hX D hD).elim

end CFSG.RankThree.PartTwo.Sec4

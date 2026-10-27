module

public import CFSG.Quasithin.Vol2.KGFactC31NoM22FusMain
public import CFSG.LocalAnalysis.SectionRank.QTK.List

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Quasithin.KGC31 CFSG.SectionRank.QTK CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def LTQTK : Prop :=
  (∀ (S : Type) [Group S] [Finite S] (p f : ℕ), p ≠ 2 → (f = 1 ∨ f = 2) →
      (StatedClassicalModel S .PSL 3 p f ∨ StatedClassicalModel S .PSU 3 p f) →
      (p ≠ 11 → SylowAutBound 11 6 S) ∧ (p = 11 → SylowAutBound 5 6 S)) ∧
  (∀ (S : Type) [Group S] [Finite S] (p : ℕ), p ≠ 2 → p ≠ 11 →
      (StatedClassicalModel S .PSp 2 p 1 ∨ ChevalleyExceptionalModel S .G2 p 1) →
      SylowAutBound 11 24 S) ∧
  (∀ (S : Type) [Group S] [Finite S] (p : ℕ), p ≠ 2 → (∃ a : ℕ, p = 2 ^ a + 1) →
      StatedClassicalModel S .PSL 4 p 1 → SylowAutBound 11 24 S) ∧
  (∀ (S : Type) [Group S] [Finite S] (p : ℕ), p ≠ 2 → (∃ b : ℕ, p + 1 = 2 ^ b) →
      StatedClassicalModel S .PSU 4 p 1 → SylowAutBound 11 24 S) ∧
  (∀ (S : Type) [Group S] [Finite S] (f : ℕ),
      (StatedClassicalModel S .PSL 3 2 f ∨ StatedClassicalModel S .PSU 3 2 f ∨
        StatedClassicalModel S .PSp 2 2 f ∨ StatedClassicalModel S .PSU 4 2 f) →
      SylowAutBound 11 1152 S) ∧
  LieSylow11Exc

@[expose] def QTKOrdNoM22 : Prop :=
  (∀ (S : Type) [Group S] [Finite S], StatedClassicalModel S .PSp 2 11 1 →
      ¬ 443520 ∣ Nat.card S) ∧
  (∀ (S : Type) [Group S] [Finite S], ChevalleyExceptionalModel S .G2 11 1 →
      ¬ 443520 ∣ Nat.card S) ∧
  (∀ (S : Type) [Group S] [Finite S], StatedClassicalModel S .PSp 3 2 1 →
      ¬ 443520 ∣ Nat.card S) ∧
  (∀ (S : Type) [Group S] [Finite S], StatedClassicalModel S .PSU 5 2 2 →
      ¬ 443520 ∣ Nat.card S) ∧
  (∀ (S : Type) [Group S] [Finite S], ReeTitsModel S .Tits 2 1 → ¬ 443520 ∣ Nat.card S) ∧
  (∀ (S : Type) [Group S] [Finite S] (f : ℕ), SuzukiModel S 2 f → ¬ 443520 ∣ Nat.card S) ∧
  (∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* NativeSporadic.Carrier .J1) →
      ¬ 443520 ∣ Nat.card S) ∧
  (∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* NativeSporadic.Carrier .J2) →
      ¬ 443520 ∣ Nat.card S) ∧
  (∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* NativeSporadic.Carrier .J3) →
      ¬ 443520 ∣ Nat.card S) ∧
  (∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* NativeSporadic.Carrier .He) →
      ¬ 443520 ∣ Nat.card S) ∧
  (∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* NativeSporadic.Carrier .Ru) →
      ¬ 443520 ∣ Nat.card S)

end CFSG.Quasithin.H13.Ch4

end

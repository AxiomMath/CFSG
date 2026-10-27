module

public import CFSG.Quasithin.Background.F7TwoInvDefs

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def InvAutGenFamL3Odd : Prop :=
  ∀ (p : ℕ) (S : Type) [Group S] [Finite S], p.Prime → p ≠ 2 → StatedClassicalModel S .PSL 3 p 1 →
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ

@[expose] def InvAutGenFamU3Odd : Prop :=
  ∀ (p : ℕ) (S : Type) [Group S] [Finite S], p.Prime → p ≠ 2 → StatedClassicalModel S .PSU 3 p 1 →
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ

@[expose] def InvAutGenFamL3Even : Prop :=
  ∀ (f : ℕ) (S : Type) [Group S] [Finite S], 2 ≤ f → StatedClassicalModel S .PSL 3 2 f →
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ

@[expose] def InvAutGenFamU3Even : Prop :=
  ∀ (f : ℕ) (S : Type) [Group S] [Finite S], 2 ≤ f → StatedClassicalModel S .PSU 3 2 f →
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ

@[expose] def InvAutGenFamSp4Even : Prop :=
  ∀ (f : ℕ) (S : Type) [Group S] [Finite S], 2 ≤ f → StatedClassicalModel S .PSp 2 2 f →
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ

@[expose] def InvAutGenFamG2Even : Prop :=
  ∀ (f : ℕ) (S : Type) [Group S] [Finite S], 2 ≤ f → ChevalleyExceptionalModel S .G2 2 f →
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ

@[expose] def InvAutGenFam3D4Even : Prop :=
  ∀ (f : ℕ) (S : Type) [Group S] [Finite S], 1 ≤ f → ChevalleyExceptionalModel S .trialityD4 2 f →
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ

@[expose] def InvAutGenFam2F4 : Prop :=
  ∀ (f : ℕ) (S : Type) [Group S] [Finite S], Odd f → 3 ≤ f → ReeTitsModel S .twistedF4 2 f →
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ

@[expose] def InvAutGenFamSz : Prop :=
  ∀ (f : ℕ) (S : Type) [Group S] [Finite S], Odd f → 3 ≤ f → SuzukiModel S 2 f →
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ

@[expose] def InvAutGenFamTits : Prop :=
  ∀ (S : Type) [Group S] [Finite S], ReeTitsModel S .Tits 2 1 →
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ

@[expose] def InvAutGenFamL5Two : Prop :=
  ∀ (S : Type) [Group S] [Finite S], StatedClassicalModel S .PSL 5 2 1 →
    ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ

@[expose] def InvAutGenFamSporadic : Prop :=
  ∀ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru) →
    ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* NativeSporadic.Carrier s) →
      ∀ φ : MulAut S, φ * φ = 1 → φ ≠ 1 → InvAutGen S φ

end CFSG.Quasithin.F7Two

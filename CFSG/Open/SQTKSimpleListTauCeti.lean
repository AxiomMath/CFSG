module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Open.SQTKTauCeti

open CFSG.Assembly CFSG.Assembly.LowTwoRank

@[expose] def StronglyQuasithin (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → pRank p (⊤ : Subgroup G) ≤ 2

@[expose] def KGroup (G : Type) [Group G] : Prop :=
  KCore.KGroupNonab InCatalog G

@[expose] def SQTKExceptional (G : Type) [Group G] : Prop :=
  ∃ i : TauCeti.ValidLieTypeIndex, Nonempty (G ≃* i.Group) ∧
    match i.val with
    | .G2 q => q.p = 2 ∧ 2 ≤ q.exponent
    | .trialityD4 q => q.p = 2 ∧ 1 ≤ q.exponent
    | .reeF4 m | .suzuki m => 1 ≤ m
    | .tits => True
    | _ => False

@[expose] def SQTKSimpleList (G : Type) [Group G] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel G .PSL 2 p f) ∨
      StatedClassicalModel G .PSL 3 p 1 ∨ StatedClassicalModel G .PSU 3 p 1)) ∨
  (∃ f : ℕ,
    (2 ≤ f ∧ StatedClassicalModel G .PSL 2 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel G .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel G .PSU 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel G .PSp 2 2 f)) ∨
  SQTKExceptional G ∨
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ StatedClassicalModel G .PSL n 2 1) ∨
  (∃ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) ∧
    Nonempty (G ≃* s.Group))

@[expose] def SQTKSimpleList_native (G : Type) [Group G] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel G .PSL 2 p f) ∨
      StatedClassicalModel G .PSL 3 p 1 ∨ StatedClassicalModel G .PSU 3 p 1)) ∨
  (∃ f : ℕ,
    (2 ≤ f ∧ StatedClassicalModel G .PSL 2 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel G .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel G .PSU 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel G .PSp 2 2 f)) ∨
  SQTKExceptional G ∨
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ StatedClassicalModel G .PSL n 2 1) ∨
  (∃ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) ∧
    Nonempty (G ≃* Blueprint.NativeSporadic.Carrier s))

end CFSG.Open.SQTKTauCeti

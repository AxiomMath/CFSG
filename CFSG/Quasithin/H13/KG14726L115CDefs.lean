module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List

public section

namespace CFSG.Quasithin.H13

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique.Ch1

@[expose] def KG115Excluded (X : Type) [Group X] : Prop :=
  ∀ (A B : Subgroup (MulAut X)) (l : X),
    (MulAut.conj : X →* MulAut X).range ≤ A → B ≤ A → ¬ 2 ∣ (B.subgroupOf A).index →
    (∃ a : ℕ, Nat.card B = 2 ^ a * 27) →
    (∃ x ∈ (MulAut.conj : X →* MulAut X).range, orderOf x = 3 ∧ x ∈ B ∧
      ∃ N : Subgroup (MulAut X), N ≤ (MulAut.conj : X →* MulAut X).range ∧ x ∈ N ∧
        B ≤ Subgroup.normalizer (N : Set (MulAut X)) ∧
        ∀ a ∈ (MulAut.conj : X →* MulAut X).range,
          a ∈ Subgroup.normalizer (N : Set (MulAut X)) → a ∈ B) →
    MulAut.conj l ∈ B → l ≠ 1 → (∀ b ∈ B, b * MulAut.conj l = MulAut.conj l * b) →
    (∀ ℓ : X, ℓ * l = l * ℓ → (orderOf ℓ).Prime → orderOf ℓ ≠ 2 → MulAut.conj ℓ ∈ B) →
    False

@[expose] def KG14726L115Spor : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName),
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .He ∨ s = .HS ∨ s = .J2 ∨
      s = .Ru) →
    CFSG.IsQuasisimple X → Nonempty ((X ⧸ CFSG.pCore 2 X) ≃* NativeSporadic.Carrier s) →
    ∀ A : Subgroup (MulAut X), (MulAut.conj : X →* MulAut X).range ≤ A →
      ∀ B : Subgroup (MulAut X), B ≤ A → ¬ 2 ∣ (B.subgroupOf A).index →
        ¬ ∃ a : ℕ, Nat.card B = 2 ^ a * 27

@[expose] def KG115L2Input : Prop :=
  ∀ (f : ℕ) (X : Type) [Group X], 2 ≤ f → StatedClassicalModel X .PSL 2 2 f → KG115Excluded X

@[expose] def KG115L3Input : Prop :=
  ∀ (f : ℕ) (X : Type) [Group X], 1 ≤ f → StatedClassicalModel X .PSL 3 2 f → KG115Excluded X

@[expose] def KG115U3Input : Prop :=
  ∀ (f : ℕ) (X : Type) [Group X], 2 ≤ f → StatedClassicalModel X .PSU 3 2 f → KG115Excluded X

@[expose] def KG115Sp4Input : Prop :=
  ∀ (f : ℕ) (X : Type) [Group X], 2 ≤ f → StatedClassicalModel X .PSp 2 2 f → KG115Excluded X

@[expose] def KG115G2Input : Prop :=
  ∀ (f : ℕ) (X : Type) [Group X], 2 ≤ f → ChevalleyExceptionalModel X .G2 2 f →
    KG115Excluded X

@[expose] def KG115D4Input : Prop :=
  ∀ (f : ℕ) (X : Type) [Group X], 1 ≤ f → ChevalleyExceptionalModel X .trialityD4 2 f →
    KG115Excluded X

@[expose] def KG115F4Input : Prop :=
  ∀ (f : ℕ) (X : Type) [Group X], Odd f → 3 ≤ f → ReeTitsModel X .twistedF4 2 f →
    KG115Excluded X

@[expose] def KG115TitsInput : Prop :=
  ∀ (X : Type) [Group X], ReeTitsModel X .Tits 2 1 → KG115Excluded X

@[expose] def KG115L33Input : Prop :=
  ∀ (X : Type) [Group X], StatedClassicalModel X .PSL 3 3 1 → KG115Excluded X

@[expose] def KG115L2pInput : Prop :=
  ∀ (p : ℕ) (X : Type) [Group X], IsFermatOrMersennePrime p → StatedClassicalModel X .PSL 2 p 1 →
    KG115Excluded X

@[expose] def KG115J4Input : Prop := KG115Excluded (NativeSporadic.Carrier .J4)

end CFSG.Quasithin.H13

end

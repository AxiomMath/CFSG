module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Defs
public import CFSG.Blueprint.NativeSporadic
public import CFSG.GroupTheory.PCore.Construction
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xKGammaLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.NativeSporadic (IsSporadic)

@[expose] def K335OddZStar : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 → CFSG.pPrimeCore 3 X = ⊥ →
    ∀ a : X, orderOf a = 3 →
      (∀ g : X, g⁻¹ * a * g * a = a * (g⁻¹ * a * g) → g⁻¹ * a * g = a) →
      ∀ y : X, a * y = y * a

@[expose] def K335SporadicOrders : Prop :=
  ∀ (X : Type) [Group X],
    (IsSporadic X .M11 → Nat.card X = 7920) ∧ (IsSporadic X .M12 → Nat.card X = 95040) ∧
    (IsSporadic X .M22 → Nat.card X = 443520) ∧ (IsSporadic X .M23 → Nat.card X = 10200960) ∧
    (IsSporadic X .HS → Nat.card X = 44352000) ∧ (IsSporadic X .J3 → Nat.card X = 50232960)

@[expose] def K335SporadicNormalizer : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (IsSporadic X .M24 ∨ IsSporadic X .J2 ∨ IsSporadic X .He ∨ IsSporadic X .Ru ∨
      IsSporadic X .J4) →
    ∀ S Q : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ → Q ≤ S → Nat.card Q = 9 →
      ∃ g ∈ Subgroup.normalizer (S : Set X), ∃ x ∈ Q, g⁻¹ * x * g ∉ Q

@[expose] def K335G2Local : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), LieModel X .G2 0 p f → p ≠ 3 →
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (H : Subgroup (GL (Fin 3) K)),
      ((p ^ f % 3 = 1 ∧ Nat.card K = p ^ f ∧ H = CFSG.Open.StatedSL 3 K) ∨
        (p ^ f % 3 = 2 ∧ Nat.card K = (p ^ f) ^ 2 ∧ H = CFSG.Open.StatedSU 3 (p ^ f) K)) ∧
      ∃ φ : ↥H →* X, Function.Injective φ ∧
        ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ ∧ S ≤ φ.range

@[expose] def K335ReeLocal : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), LieModel X .twistedF4 0 2 f →
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), Nat.card K = (2 ^ f) ^ 2 ∧
      ∃ φ : ↥(CFSG.Open.StatedSU 3 (2 ^ f) K) →* X, Function.Injective φ ∧
        ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 3 S ⊤ ∧ S ≤ φ.range

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

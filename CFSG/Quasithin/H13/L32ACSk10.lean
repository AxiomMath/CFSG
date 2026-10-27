module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3Structure315Defs

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def LieSylowOver3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 < n → CFSG.IsQuasisimple X →
    Odd (Nat.card (Subgroup.center X)) → A315.IsLieChar2 n (X ⧸ Subgroup.center X) →
    ∀ S Y : Subgroup X, IsSylowTwoOf S ⊤ → S ≤ Y → S.relIndex Y = 3 →
      Y ≤ Subgroup.normalizer (S : Set X)

@[expose] def LieBorelInvert3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 < n → CFSG.IsQuasisimple X →
    Odd (Nat.card (Subgroup.center X)) → A315.IsLieChar2 n (X ⧸ Subgroup.center X) →
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ∀ α : MulAut X, (∃ k : ℕ, α ^ 2 ^ k = 1) →
      S.map α.toMonoidHom = S →
      ∀ y ∈ Subgroup.normalizer (S : Set X), y ∉ S → y ^ 3 ∈ S → α y * y ∈ S →
      ∀ D : Subgroup X, S ≤ D → D ≤ Subgroup.normalizer (S : Set X) → y ∉ D →
        D.relIndex (Subgroup.normalizer (S : Set X)) = 3 → (∀ d ∈ D, α d * d⁻¹ ∈ S) →
        IsPSL 2 2 2 (X ⧸ Subgroup.center X) ∨ IsPSU 3 2 3 (X ⧸ Subgroup.center X) ∨
          IsPSL 3 2 2 (X ⧸ Subgroup.center X)

@[expose] def LieBorelThreeInner : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 < n → CFSG.IsQuasisimple X →
    Odd (Nat.card (Subgroup.center X)) → A315.IsLieChar2 n (X ⧸ Subgroup.center X) →
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ∀ α β : MulAut X, (∃ k : ℕ, α ^ 2 ^ k = 1) →
      β ^ 3 = 1 → S.map α.toMonoidHom = S → S.map β.toMonoidHom = S → α * β * α⁻¹ = β⁻¹ →
      (∀ b ∈ Subgroup.normalizer (S : Set X), α b * b⁻¹ ∈ S) →
      (∀ b ∈ Subgroup.normalizer (S : Set X), β b * b⁻¹ ∈ S) →
      β ∈ (MulAut.conj : X →* MulAut X).range ∨ IsPSL 3 2 2 (X ⧸ Subgroup.center X)

@[expose] def LieBorelTwoInner : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 < n → CFSG.IsQuasisimple X →
    Odd (Nat.card (Subgroup.center X)) → A315.IsLieChar2 n (X ⧸ Subgroup.center X) →
    CFSG.pRank 3 X = 1 →
    ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ∀ α : MulAut X, (∃ k : ℕ, α ^ 2 ^ k = 1) →
      S.map α.toMonoidHom = S → (∀ b ∈ Subgroup.normalizer (S : Set X), α b * b⁻¹ ∈ S) →
      ∃ s ∈ S, α = MulAut.conj s

end CFSG.Quasithin.H13.L32A.C

module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanCharTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs

public section

open Module Multiplicative QuadraticMap Matrix

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal

@[expose] def OrthRankOneModelInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ (A : Subgroup (V ≃ₗ[K] V)), A ≤ orthDerived Q → ∀ (r : ℕ) (Δ : TBJOmData Q p A r), 3 ≤ r →
      4 ≤ Nat.card K → (∀ v : V, (∀ a ∈ A, a v = v) → v = 0) → Δ.RankOneModel

@[expose] def OrthPairModelInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ (A : Subgroup (V ≃ₗ[K] V)), A ≤ orthDerived Q → ∀ (r : ℕ) (Δ : TBJOmData Q p A r), 3 ≤ r →
      p ∣ Nat.card K + 1 → (∀ v : V, (∀ a ∈ A, a v = v) → v = 0) →
      ∀ (f : ℕ), Nat.card K = 2 ^ f → ∀ (K' : Type) [Field K'] [Finite K'] [CharP K' 2],
        Nat.card K' = (2 ^ f) ^ 2 → Δ.PairModel f K'

@[expose] def OrthGenModelInput :
    Prop :=
  PhanDInput2 → ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (p : ℕ) [Fact p.Prime], p ≠ 2 →
    ∀ (A : Subgroup (V ≃ₗ[K] V)), A ≤ orthDerived Q → ∀ (r : ℕ) (Δ : TBJOmData Q p A r), 4 ≤ r →
      4 ≤ Nat.card K → p ∣ Nat.card K + 1 → (∀ v : V, (∀ a ∈ A, a v = v) → v = 0) →
      ∀ (f : ℕ), Nat.card K = 2 ^ f → ∀ (K' : Type) [Field K'] [Finite K'] [CharP K' 2],
        Nat.card K' = (2 ^ f) ^ 2 → Δ.RankOneModel → Δ.PairModel f K' →
        (Even r → Nonempty ((lieUniversal .POmegaPlus r 2 f Nat.prime_two).K ≃* ↥(orthDerived Q))) →
        (Odd r → Nonempty ((lieUniversal .POmegaMinus r 2 f Nat.prime_two).K ≃* ↥(orthDerived Q))) →
        (⨆ (i : Fin r) (j : Fin r) (_ : i ≠ j), (Δ.rankOne i j ⊔ Δ.rankOnePos i j)) = orthDerived Q

end OrthTorus

end CFSG.StandardType

end

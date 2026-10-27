module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG
open CFSG.Assembly (InCatalog)

@[expose] def FF84KF1 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → InCatalog K →
    ∀ P : Sylow 3 K, Nat.card (P : Subgroup K) = 9 → ¬ IsCyclic (P : Subgroup K) →
    ∀ P₁ : Subgroup K, P₁ ≤ P → Nat.card P₁ = 3 →
      ¬ (Subgroup.normalizer ((P : Subgroup K) : Set K) ≤ Subgroup.normalizer (P₁ : Set K))

@[expose] def FF84KSOut : Prop :=
  ∀ (C : Type) [Group C] [Finite C], IsSimpleGroup C → (∃ a b : C, a * b ≠ b * a) → InCatalog C →
    3 ∣ Nat.card C → ¬ 9 ∣ Nat.card C →
    ∀ α : MulAut C, α ^ 3 = 1 → ∃ c : C, α = MulAut.conj c

end CFSG.RankThree.PartTwo.Sec21.FF84

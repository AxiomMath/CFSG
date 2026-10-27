module

public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin

section A6Fin

variable {W : Type} [CommGroup W]

@[expose] def A6Fuses {L : Type} [Group L] (β : L ≃* L) : Prop :=
  ∃ x : L, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l : L, l * x * l⁻¹ ≠ β x

@[expose] def A6QuadPair (a b : MulAut W) : Prop :=
  ∀ w : W, a ((b w) * w⁻¹) * ((b w) * w⁻¹)⁻¹ = 1

@[expose] noncomputable def A6Rank (g : MulAut W) : ℕ := rkIdx (fixV (Subgroup.zpowers g))

end A6Fin

@[expose] def A6Fin : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → Nat.card W = 16 →
    ∀ L : Subgroup (MulAut W), Nonempty (L ≃* alternatingGroup (Fin 6)) →
      (∀ S : Subgroup W, (∀ l ∈ L, ∀ w ∈ S, l w ∈ S) → S = ⊥ ∨ S = ⊤) →
      (∀ n : MulAut W, (∀ l ∈ L, n * l = l * n) → n = 1) ∧
      (∀ l ∈ L, l ≠ 1 → l ^ 2 = 1 → A6Rank l = 2) ∧
      (∀ n₁ ∈ Subgroup.normalizer (L : Set (MulAut W)), ∀ n₂ ∈ Subgroup.normalizer (L : Set (MulAut W)),
          n₁ ∉ L → n₂ ∉ L → n₁⁻¹ * n₂ ∈ L) ∧
      ∀ β : L ≃* L, A6Fuses β →
        (¬ ∃ n : MulAut W, ∀ l : L, n * (l : MulAut W) * n⁻¹ = (β l : MulAut W)) ∧
        (∀ n ∈ Subgroup.normalizer (L : Set (MulAut W)), ∀ n' ∈ Subgroup.normalizer (L : Set (MulAut W)),
          n ^ 2 = 1 → n' ^ 2 = 1 → n ∉ L → n' ∉ L →
          (∀ l l'' : L, n' * (l : MulAut W) * n'⁻¹ = (l'' : MulAut W) →
            n * (β l : MulAut W) * n⁻¹ = (β l'' : MulAut W)) →
          3 ≤ A6Rank n + A6Rank n') ∧
        (∀ a b : L, a ≠ b → a ≠ 1 → b ≠ 1 → a ^ 2 = 1 → b ^ 2 = 1 → a * b = b * a →
          ¬ (A6QuadPair (a : MulAut W) (b : MulAut W) ∧
              A6QuadPair (β.symm a : MulAut W) (β.symm b : MulAut W)))

end CFSG.Quasithin

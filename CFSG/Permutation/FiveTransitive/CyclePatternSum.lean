module

public import CFSG.Permutation.FiveTransitive.CyclePatternRoots

public section

namespace CFSG

namespace FiveTransitive.CyclePatternSum

open Equiv CyclePatternRoots

variable {X I J : Type*}

@[expose] def sumEquiv (g : Perm X) (π : Perm I) (σ : Perm J) :
    Pattern g (π.sumCongr σ) ≃
      (Σ a : Pattern g π, {b : Pattern g σ // ∀ i j, a.val i ≠ b.val j}) where
  toFun e := ⟨⟨⟨fun i => e.val (Sum.inl i), fun _ _ h => Sum.inl_injective (e.val.injective h)⟩,
      fun i => e.property (Sum.inl i)⟩,
    ⟨⟨⟨fun j => e.val (Sum.inr j), fun _ _ h => Sum.inr_injective (e.val.injective h)⟩,
      fun j => e.property (Sum.inr j)⟩,
      fun i j h => Sum.inl_ne_inr (e.val.injective h)⟩⟩
  invFun e := ⟨⟨Sum.elim e.1.val e.2.val.val, by
    intro i j h
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (e.1.val.injective h)
      | inr j => exact (e.2.property i j h).elim
    | inr i =>
      cases j with
      | inl j => exact (e.2.property j i h.symm).elim
      | inr j => exact congrArg Sum.inr (e.2.val.val.injective h)⟩, by
    intro i
    cases i with
    | inl i => exact e.1.property i
    | inr i => exact e.2.val.property i⟩
  left_inv e := by
    apply Subtype.ext
    ext i
    cases i <;> rfl
  right_inv e := by
    apply Sigma.ext
    · rfl
    · rfl

theorem card_sum_of_disjoint [Finite X] [Finite I] [Finite J]
    (g : Perm X) (π : Perm I) (σ : Perm J)
    (hdis : ∀ (a : Pattern g π) (b : Pattern g σ) i j, a.val i ≠ b.val j) :
    Nat.card (Pattern g (π.sumCongr σ)) =
      Nat.card (Pattern g π) * Nat.card (Pattern g σ) := by
  classical
  let E : (Σ a : Pattern g π, {b : Pattern g σ // ∀ i j, a.val i ≠ b.val j}) ≃
      Pattern g π × Pattern g σ :=
    { toFun := fun e => (e.1,e.2.val)
      invFun := fun e => ⟨e.1,⟨e.2,hdis e.1 e.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr ((sumEquiv g π σ).trans E), Nat.card_prod]

end FiveTransitive.CyclePatternSum

end CFSG

module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43

open Equiv CFSG.Quasithin.F53Mod

@[expose] def M17Orth : Prop :=
  ∀ (W : Model 5) (F : Subgroup W.W) (φ : orth.W ≃* ↥F),
    (∀ (σ : Perm (Fin 5)) (u : orth.W),
      ((φ (orth.act σ u) : ↥F) : W.W) = W.act σ ((φ u : ↥F) : W.W)) →
    (∀ σ ∈ alternatingGroup (Fin 5), ∀ w : W.W, W.act σ w * w⁻¹ ∈ F) →
    (∀ w : W.W, (∀ σ ∈ alternatingGroup (Fin 5), W.act σ w = w) → w = 1) → F = ⊤

@[expose] def M17Nat : Prop :=
  ∀ (W : Model 5) (F : Subgroup W.W) (φ : nat.W ≃* ↥F),
    (∀ (σ : Perm (Fin 5)) (u : nat.W),
      ((φ (nat.act σ u) : ↥F) : W.W) = W.act σ ((φ u : ↥F) : W.W)) →
    (∀ σ ∈ alternatingGroup (Fin 5), ∀ w : W.W, W.act σ w * w⁻¹ ∈ F) →
    (∀ w : W.W, (∀ σ ∈ alternatingGroup (Fin 5), W.act σ w = w) → w = 1) →
    ∀ B : Subgroup W.W, (∀ σ ∈ S5That, ∀ b ∈ B, W.act σ b = b) → B ⊔ F = ⊤ →
      F.relIndex ⊤ ≤ 2 ∧ Nat.card B ≤ 4 ∧ Nat.card ↥(B ⊓ F) ≤ 2

end CFSG.Quasithin.F53.Stellmacher.S43

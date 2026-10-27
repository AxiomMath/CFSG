module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TArc

public section

namespace CFSG.Quasithin.Fan86.Tutte

open CFSG.Quasithin.F6.GoldAmL3T

@[expose] def TutteRegular : Prop :=
  ∀ (W : Type) (Γ : SimpleGraph W), Γ.IsTree → (∀ w, Nat.card (Γ.neighborSet w) = 3) →
  ∀ (H : Type) [Group H] [MulAction H W],
    (∀ (h : H) (u v : W), Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v) →
  ∀ s : ℕ, 1 ≤ s → (∀ P Q : Arc Γ s, ∃ h : H, ∀ i, i ≤ s → h • P.vert i = Q.vert i) →
  (∀ (P : Arc Γ s) (h : H), (∀ i, i ≤ s → h • P.vert i = P.vert i) → ∀ w : W, h • w = w) →
    s ≤ 5

@[expose] def TutteTree : Prop :=
  ∀ (W : Type) (Γ : SimpleGraph W), Γ.IsTree → (∀ w, Nat.card (Γ.neighborSet w) = 3) →
  ∀ (H : Type) [Group H] [MulAction H W],
    (∀ (h : H) (u v : W), Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v) →
  (∀ u v : W, ∃ h : H, h • u = v) → (∀ w : W, Finite (MulAction.stabilizer H w)) →
  (∀ w u v : W, Γ.Adj w u → Γ.Adj w v → ∃ h ∈ MulAction.stabilizer H w, h • u = v) →
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 5 ∧ ∀ (P : Arc Γ k) (h : H), (∀ i, i ≤ k → h • P.vert i = P.vert i) →
      ∀ w : W, h • w = w

end CFSG.Quasithin.Fan86.Tutte

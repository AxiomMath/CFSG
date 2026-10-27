module

public import CFSG.LocalAnalysis.StandardType.FS81.HMCore
public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreE7P
public import CFSG.LocalAnalysis.StandardType.FS81.AutMat

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix

@[expose] def qE8 (e : Coords 8) : ZMod 3 :=
  2 * (e 0 ^ 2 + e 1 ^ 2) + ∑ i : Fin 6, e i.succ.succ ^ 2

@[expose] def E8RootLine (δ : ZMod 3) (e : Coords 8) : Prop :=
  (wt e = 1 ∧ (e 0 ≠ 0 ∨ e 1 ≠ 0)) ∨ (wt e = 2 ∧ e 0 = 0 ∧ e 1 = 0) ∨
    (wt e = 3 ∧ e 0 ≠ 0 ∧ e 1 ≠ 0) ∨
    (wt e = 7 ∧ e 0 = 0 ∧ ∏ i : Fin 6, e i.succ.succ = δ) ∨
    (wt e = 7 ∧ e 1 = 0 ∧ ∏ i : Fin 6, e i.succ.succ = -δ)

@[expose] def E7MatCore : Prop :=
  ∀ X : Subgroup (GL (Fin 8) (ZMod 3)),
    (∀ A ∈ hSeven, ∃ x ∈ X, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) = A) →
    (∀ x ∈ X, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      (∃ c : ZMod 3, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 1 1 = c • Pi.single 1 1) →
        (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ hSeven) →
    Nat.card ↥(X ⊓ fixE0 7) = 2903040 →
    (∀ x ∈ X, (x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      ∀ v : Coords 8, v 0 = 0 → ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ v) 0 = 0) →
    (∀ N : Subgroup ↥X, N.Normal → Odd (Nat.card N) → N = ⊥) →
    (∃ x ∈ X, ∃ i : Fin 8, i ≠ 0 ∧ ((x : Matrix (Fin 8) (Fin 8) (ZMod 3)) *ᵥ Pi.single 0 1) i ≠ 0) →
      ∃ δ : ZMod 3, (δ = 1 ∨ δ = -1) ∧ Nat.card X = 696729600 ∧
        (∀ e : Coords 8, e ≠ 0 → (OrbitLine X (Pi.single 0 1) e ↔ E8RootLine δ e)) ∧
        (∀ e : Coords 8, e ≠ 0 → (OrbitLine X (Pi.single 0 1 + Pi.single 1 1) e ↔ qE8 e = 1))

end CFSG.StandardType.FrameRoute.FS81

end

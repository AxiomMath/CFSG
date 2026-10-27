module

public import CFSG.Quasithin.Recognition.UniquenessSystemDefs

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94

universe u

variable {V : Type u} (Δ : SimpleGraph V)

@[expose] def Perp (x y : V) : Prop := x = y ∨ Δ.Adj x y

@[expose] def Dist2 (x y : V) : Prop := x ≠ y ∧ ¬ Δ.Adj x y ∧ ∃ w, Δ.Adj x w ∧ Δ.Adj w y

@[expose] def Within2 (x y : V) : Prop := Perp Δ x y ∨ ∃ w, Δ.Adj x w ∧ Δ.Adj w y

@[expose] def FourGenerated : Prop :=
  ∀ c : List V, IsCycle Δ c → InClosure Δ {p | IsNGon Δ 3 p ∨ IsNGon Δ 4 p} c

structure HypA (N : ℕ) (R : ℕ → V → V → Prop) : Prop where
  symm : ∀ k x y, R k x y → R k y x
  mono : ∀ k < N, ∀ x y, R k x y → R (k + 1) x y
  zero : ∀ x y, R 0 x y ↔ Perp Δ x y
  top : ∀ x y, R N x y ↔ Within2 Δ x y
  a2 : ∀ k < N, ∀ x y z, R (k + 1) x y → Dist2 Δ x y → Dist2 Δ x z →
    ∃ u v, R k y u ∧ Δ.Adj x u ∧ Δ.Adj x v ∧ Δ.Adj z v ∧ R (min k 1) u v

@[expose] def comp (x u y w : V) : Prop :=
  ∃ (hu : Δ.Adj x u ∧ Δ.Adj y u) (hw : Δ.Adj x w ∧ Δ.Adj y w),
    (Δ.induce {a | Δ.Adj x a ∧ Δ.Adj y a}).Reachable ⟨u, hu⟩ ⟨w, hw⟩

@[expose] def induced (R : ℕ → V → V → V → Prop) (k : ℕ) (x y : V) : Prop :=
  Perp Δ x y ∨ ∃ u, R k x u y

@[expose] def dSet (R : ℕ → V → V → V → Prop) (k : ℕ) (x u y w : V) : Prop :=
  comp Δ x u y w ∨ (Δ.Adj x w ∧ ∃ c, comp Δ x u y c ∧ R k y c w)

structure HypB (N : ℕ) (R : ℕ → V → V → V → Prop) : Prop where
  symm : ∀ k x u y, R k x u y → R k y u x
  mono : ∀ k < N, ∀ x u y, R k x u y → R (k + 1) x u y
  zero : ∀ x u y, R 0 x u y ↔ (Δ.Adj x u ∧ Δ.Adj u y ∧ Δ.Adj x y)
  top : ∀ x u y, R N x u y ↔ (Δ.Adj x u ∧ Δ.Adj u y ∧ x ≠ y)
  b2 : ∀ k < N, ∀ x u y v z, R (k + 1) x u y → ¬ R 0 x u y → R N x v z → ¬ R 0 x v z →
    ∃ a b, dSet Δ R k x u y a ∧ comp Δ x v z b ∧ induced Δ R (min k 1) a b
  b3 : ∀ x y w, induced Δ R 1 x y → Dist2 Δ x y → Δ.Adj y w → Dist2 Δ x w →
    ∃ a, Δ.Adj x a ∧ Δ.Adj y a ∧ Perp Δ a w

end CFSG.Quasithin.H13.AS91

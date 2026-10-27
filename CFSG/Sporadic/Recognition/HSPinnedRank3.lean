module

public import CFSG.Sporadic.Recognition.HSPinnedCert
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Sporadic.Recognition.HSPinned

open CFSG.Sporadic.Recognition.HSPinned.Native

theorem adjB_irrefl (x : ℕ) (hx : x < 100) : adjB x x = false := by
  have := adj_spec x hx x hx
  simp only [ne_eq, not_true_eq_false, false_and, iff_false] at this
  simpa using this

theorem adjB_symm {x y : ℕ} (hx : x < 100) (hy : y < 100) :
    adjB x y = true → adjB y x = true := by
  rw [adj_spec x hx y hy, adj_spec y hy x hx]
  rintro ⟨hne, t, h1, h2⟩
  exact ⟨hne.symm, t, h2, h1⟩

@[expose] def sigmaExplicit : SimpleGraph (Fin 100) where
  Adj x y := adjB x.val y.val = true
  symm := ⟨fun x y h => adjB_symm x.isLt y.isLt h⟩
  loopless := ⟨fun x h => by rw [adjB_irrefl x.val x.isLt] at h; exact absurd h (by simp)⟩

instance : DecidableRel sigmaExplicit.Adj := fun x y =>
  inferInstanceAs (Decidable (adjB x.val y.val = true))

theorem sigmaExplicit_adj
    {x y : Fin 100} : sigmaExplicit.Adj x y ↔ adjB x.val y.val = true :=
  Iff.rfl

@[expose] def orbitalGraph (G : Type*) [Group G] {X : Type*} [MulAction G X] (a b : X) :
    SimpleGraph X :=
  SimpleGraph.fromRel fun x y => ∃ g : G, g • a = x ∧ g • b = y

end CFSG.Sporadic.Recognition.HSPinned

module

public import CFSG.LocalAnalysis.StandardType.GGNineDepDefs
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure GGSmallLinHyp (p N : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) {T : Type} (s : T → (V ≃ₗ[ZMod p] V)) (x : V) :
    Prop where
  p_ne_two : p ≠ 2
  p_dvd : p ∣ N
  dim_le : Module.finrank (ZMod p) V ≤ N
  pair : ∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)
  refl_form : ∀ i v, r i v = v - α i v • h i
  finT : Finite T
  s_refl : ∀ k, GGLinRefl (s k)
  conn : (SimpleGraph.fromRel fun i j => s i * s j ≠ s j * s i).Connected
  x_ne : x ≠ 0
  fix_s : ggLinFix (Set.range s) = Submodule.span (ZMod p) {x}
  x_not_fix : x ∉ ggLinFix (Set.range r)
  no_transv : ∀ g ∈ Subgroup.closure (Set.range r ∪ Set.range s),
    ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)

@[expose] def GGSmallDepFixLineAt (p N : ℕ) [Fact p.Prime] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] (h : Fin (N - 1) → V)
    (α : Fin (N - 1) → Module.Dual (ZMod p) V) (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (T : Type)
    (s : T → (V ≃ₗ[ZMod p] V)) (x : V), GGSmallLinHyp p N h α r s x →
    ¬ LinearIndependent (ZMod p) h →
    Nat.card ↥(ggLargeGrp r s ⊓ MulAction.stabilizer (V ≃ₗ[ZMod p] V) x) ≤
      6 * (p - 1) * Nat.card ↥(Subgroup.closure (Set.range s)) →
    (∃ M : CoxeterMatrix (Fin (N - 1)), GGIsWeylMatrix M ∧
      Nonempty (M.Group ≃* ↥(Subgroup.closure (Set.range s)))) →
    Module.finrank (ZMod p) ↥(ggLinFix (Set.range r)) ≤ 1

@[expose] def GGSmallDepCaseIAt (p N : ℕ) [Fact p.Prime] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V) (x : V),
    p ≠ 2 → Module.finrank (ZMod p) V = N →
    GGDepAFrame p N h α x →
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) → (∀ i v, r i v = v - α i v • h i) →
    (ra : V ≃ₗ[ZMod p] V) → (ha : V) → (αa : Module.Dual (ZMod p) V) →
    (∀ v, ra v = v - αa v • ha) → αa ha = 2 → (∃ c, αa (h c) ≠ 0) →
    αa x ≠ 0 →
    (∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) →
    Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N) →
    ha ∉ Submodule.span (ZMod p) (Set.range h) → False

@[expose] def GGSmallDepCaseIIAt (p N : ℕ) [Fact p.Prime] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V) (x : V),
    p ≠ 2 → Module.finrank (ZMod p) V = N →
    GGDepAFrame p N h α x →
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) → (∀ i v, r i v = v - α i v • h i) →
    (ra : V ≃ₗ[ZMod p] V) → (ha : V) → (αa : Module.Dual (ZMod p) V) →
    (∀ v, ra v = v - αa v • ha) → αa ha = 2 →
    αa x ≠ 0 →
    (∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) →
    Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N) →
    ha ∈ Submodule.span (ZMod p) (Set.range h) → False

@[expose] def GGSmallD1Input : Prop :=
  ∀ (p N : ℕ) [Fact p.Prime],
    (p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7) ∨ (p = 5 ∧ N = 10) →
    GGSmallDepFixLineAt p N

@[expose] def GGSmallD2Input : Prop :=
  ∀ (p N : ℕ) [Fact p.Prime], (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7) ∨ (p = 5 ∧ N = 10) →
    GGSmallDepCaseIAt p N ∧ GGSmallDepCaseIIAt p N

end CFSG.StandardType

end

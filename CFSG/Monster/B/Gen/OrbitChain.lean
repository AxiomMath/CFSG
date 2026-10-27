module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Monster.B

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def chainStab (b : ℕ → X) (i : ℕ) : Subgroup G where
  carrier := {g | ∀ k < i, g • b k = b k}
  one_mem' k _ := one_smul G (b k)
  mul_mem' {g h} hg hh k hk := by
    rw [mul_smul, hh k hk, hg k hk]
  inv_mem' {g} hg k hk := by
    rw [inv_smul_eq_iff, hg k hk]

theorem mem_chainStab {b : ℕ → X} {i : ℕ} {g : G} : g ∈ chainStab b i ↔ ∀ k < i, g • b k = b k :=
  Iff.rfl

theorem chainStab_zero (b : ℕ → X) : chainStab (G := G) b 0 = ⊤ := by
  ext g
  simp [mem_chainStab]

variable [Finite G]

theorem card_mul_le_card_chainStab (b : ℕ → X) (i : ℕ) (P : Finset X)
    (hP : ∀ p ∈ P, ∃ g ∈ chainStab (G := G) b i, g • b i = p) :
    P.card * Nat.card (chainStab (G := G) b (i + 1)) ≤ Nat.card (chainStab (G := G) b i) := by
  set S := chainStab (G := G) b i
  have horb : Nat.card (MulAction.orbit S (b i)) * Nat.card (MulAction.stabilizer S (b i)) =
      Nat.card S := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, mul_comm]
    exact Subgroup.card_mul_index _
  have hsub : (P : Set X) ⊆ MulAction.orbit S (b i) := by
    intro p hp
    obtain ⟨g, hg, rfl⟩ := hP p hp
    exact ⟨⟨g, hg⟩, rfl⟩
  have hfin : (MulAction.orbit S (b i)).Finite := Set.finite_range _
  have hP' : P.card ≤ Nat.card (MulAction.orbit S (b i)) := by
    rw [← Set.ncard_coe_finset, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub hfin
  have hstab : Nat.card (MulAction.stabilizer S (b i)) = Nat.card (chainStab (G := G) b (i + 1)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, fun k hk => ?_⟩
        invFun := fun y => ⟨⟨y.1, fun k hk => y.2 k (by omega)⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact x.1.2 k hk
      · exact x.2
    · exact y.2 i (by omega)
  calc P.card * Nat.card (chainStab (G := G) b (i + 1))
      ≤ Nat.card (MulAction.orbit S (b i)) * Nat.card (MulAction.stabilizer S (b i)) := by
        rw [hstab]
        exact Nat.mul_le_mul_right _ hP'
    _ = Nat.card S := horb

theorem card_ge_prod_of_chain (b : ℕ → X) (P : ℕ → Finset X) (m : ℕ)
    (hP : ∀ i < m, ∀ p ∈ P i, ∃ g : G, (∀ k < i, g • b k = b k) ∧ g • b i = p) :
    ∏ i ∈ Finset.range m, (P i).card ≤ Nat.card G := by
  have key : ∀ n ≤ m, (∏ i ∈ Finset.range n, (P i).card) * Nat.card (chainStab (G := G) b n) ≤
      Nat.card G := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Finset.prod_range_zero, one_mul, chainStab_zero, Subgroup.card_top]
    | succ n ih =>
      intro hn
      have hstep := card_mul_le_card_chainStab (G := G) b n (P n) (fun p hp => by
        obtain ⟨g, hg, hgp⟩ := hP n (by omega) p hp
        exact ⟨g, hg, hgp⟩)
      calc (∏ i ∈ Finset.range (n + 1), (P i).card) * Nat.card (chainStab (G := G) b (n + 1))
          = (∏ i ∈ Finset.range n, (P i).card) *
              ((P n).card * Nat.card (chainStab (G := G) b (n + 1))) := by
            rw [Finset.prod_range_succ, mul_assoc]
        _ ≤ (∏ i ∈ Finset.range n, (P i).card) * Nat.card (chainStab (G := G) b n) :=
            Nat.mul_le_mul_left _ hstep
        _ ≤ Nat.card G := ih (by omega)
  have h := key m le_rfl
  have hpos : 0 < Nat.card (chainStab (G := G) b m) := Nat.card_pos
  calc ∏ i ∈ Finset.range m, (P i).card
      ≤ (∏ i ∈ Finset.range m, (P i).card) * Nat.card (chainStab (G := G) b m) :=
        Nat.le_mul_of_pos_right _ hpos
    _ ≤ Nat.card G := h

end CFSG.Monster.B

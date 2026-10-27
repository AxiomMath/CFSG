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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.G64

variable {M : Type*} [Group M]

theorem mem_sup_of_normalizer {A B : Subgroup M} (hAB : A ≤ Subgroup.normalizer (B : Set M))
    {x : M} (hx : x ∈ A ⊔ B) : ∃ y ∈ A, ∃ z ∈ B, x = y * z := by
  have hx' : x ∈ ((A ⊔ B : Subgroup M) : Set M) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAB] at hx'
  obtain ⟨y, hy, z, hz, rfl⟩ := hx'
  exact ⟨y, hy, z, hz, rfl⟩

theorem mem_normalizer_of_conj_mem [Finite M] {H : Subgroup M} {y : M}
    (h : ∀ x ∈ H, y * x * y⁻¹ ∈ H) : y ∈ Subgroup.normalizer (H : Set M) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]

theorem mem_normalizer_sup {A B : Subgroup M} {y : M}
    (hA : y ∈ Subgroup.normalizer (A : Set M)) (hB : y ∈ Subgroup.normalizer (B : Set M)) :
    y ∈ Subgroup.normalizer ((A ⊔ B : Subgroup M) : Set M) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem le_normalizer_of_commute {A B : Subgroup M} (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    A ≤ Subgroup.normalizer (B : Set M) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h x hx y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 := h x hx _ hy
    have : x * y * x⁻¹ = y := by
      calc x * y * x⁻¹ = x⁻¹ * (x * (x * y * x⁻¹)) := by group
        _ = x⁻¹ * ((x * y * x⁻¹) * x) := by rw [h1]
        _ = y := by group
    rw [← this]
    exact hy

theorem mem_closure_inter_of_mem {A B : Subgroup M} {D : Set M} (hAB : A ⊓ B = ⊥)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hD : ∀ d ∈ D, d ∈ A ∨ d ∈ B) {x : M}
    (hx : x ∈ Subgroup.closure D) (hxA : x ∈ A) : x ∈ Subgroup.closure {d | d ∈ D ∧ d ∈ A} := by
  set DA := Subgroup.closure {d | d ∈ D ∧ d ∈ A} with hDA
  set DB := Subgroup.closure {d | d ∈ D ∧ d ∈ B} with hDB
  have hDAA : DA ≤ A := (Subgroup.closure_le _).2 fun d hd => hd.2
  have hDBB : DB ≤ B := (Subgroup.closure_le _).2 fun d hd => hd.2
  have hle : Subgroup.closure D ≤ DA ⊔ DB := by
    rw [Subgroup.closure_le]
    intro d hd
    rcases hD d hd with h | h
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨hd, h⟩)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨hd, h⟩)
  have hn : DA ≤ Subgroup.normalizer (DB : Set M) :=
    le_normalizer_of_commute fun y hy z hz => hcomm y (hDAA hy) z (hDBB hz)
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup_of_normalizer hn (hle hx)
  have hzA : z ∈ A := by
    have := A.mul_mem (A.inv_mem (hDAA hy)) hxA
    simpa using this
  have hz1 : z = 1 := by
    have : z ∈ A ⊓ B := ⟨hzA, hDBB hz⟩
    rw [hAB, Subgroup.mem_bot] at this
    exact this
  rw [hz1, mul_one]
  exact hy

theorem sq_mem_of_cyclic_mod {H N : Subgroup M} {D : Set M} {y : M} (hDH : Subgroup.closure D = H)
    (hD : ∀ d ∈ D, d ^ 2 = 1) (hHN : H ≤ Subgroup.normalizer (N : Set M))
    (hyH : y ∈ H) (hform : ∀ x ∈ H, ∃ n ∈ N, ∃ j : ℤ, x = n * y ^ j) : y ^ 2 ∈ N := by
  have hconj : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.1 (hHN hg) n).1 hn
  have hyj : ∀ j : ℤ, y ^ j ∈ H := fun j => H.zpow_mem hyH j
  have hcomm : ∀ x ∈ H, ∀ z ∈ H, x * z * x⁻¹ * z⁻¹ ∈ N := by
    intro x hx z hz
    obtain ⟨n, hn, i, rfl⟩ := hform x hx
    obtain ⟨n', hn', j, rfl⟩ := hform z hz
    have : n * y ^ i * (n' * y ^ j) * (n * y ^ i)⁻¹ * (n' * y ^ j)⁻¹ =
        n * (y ^ i * n' * (y ^ i)⁻¹) * (y ^ j * n⁻¹ * (y ^ j)⁻¹) * n'⁻¹ := by
      have hij : y ^ i * y ^ j = y ^ j * y ^ i := by rw [← zpow_add, ← zpow_add, add_comm]
      calc n * y ^ i * (n' * y ^ j) * (n * y ^ i)⁻¹ * (n' * y ^ j)⁻¹
          = n * (y ^ i * n' * (y ^ i)⁻¹) * ((y ^ i * y ^ j) * (y ^ i)⁻¹ * n⁻¹ * (y ^ j)⁻¹)
              * n'⁻¹ := by group
        _ = n * (y ^ i * n' * (y ^ i)⁻¹) * ((y ^ j * y ^ i) * (y ^ i)⁻¹ * n⁻¹ * (y ^ j)⁻¹)
              * n'⁻¹ := by rw [hij]
        _ = _ := by group
    rw [this]
    refine N.mul_mem (N.mul_mem (N.mul_mem hn (hconj _ (hyj i) _ hn')) ?_) (N.inv_mem hn')
    exact hconj _ (hyj j) _ (N.inv_mem hn)
  let S : Subgroup M :=
    { carrier := {x | x ∈ H ∧ x ^ 2 ∈ N}
      one_mem' := ⟨H.one_mem, by simp [N.one_mem]⟩
      mul_mem' := by
        rintro x z ⟨hx, hx2⟩ ⟨hz, hz2⟩
        refine ⟨H.mul_mem hx hz, ?_⟩
        have h1 := hcomm x hx z hz
        have : (x * z) ^ 2 = (x * z * x⁻¹ * z⁻¹) * (z * x ^ 2 * z⁻¹) * z ^ 2 := by
          rw [pow_two, pow_two, pow_two]
          group
        rw [this]
        exact N.mul_mem (N.mul_mem h1 (hconj z hz _ hx2)) hz2
      inv_mem' := by
        rintro x ⟨hx, hx2⟩
        refine ⟨H.inv_mem hx, ?_⟩
        rw [inv_pow]
        exact N.inv_mem hx2 }
  have hHS : H ≤ S := by
    rw [← hDH, Subgroup.closure_le]
    intro d hd
    have hdH : d ∈ H := hDH ▸ Subgroup.subset_closure hd
    exact ⟨hdH, by rw [hD d hd]; exact N.one_mem⟩
  exact (hHS hyH).2

@[expose] def fixPt {V : Type*} [Group V] (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {x | ∀ w ∈ W, x w = w}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {x y} hx hy w hw => by
    show x (y w) = w
    rw [hy w hw, hx w hw]
  inv_mem' := fun {x} hx w hw => by
    show x.symm w = w
    rw [MulEquiv.symm_apply_eq]
    exact (hx w hw).symm

theorem mem_fixPt {V : Type*} [Group V] {W : Subgroup V} {x : MulAut V} :
    x ∈ fixPt W ↔ ∀ w ∈ W, x w = w := Iff.rfl

end CFSG.Quasithin.G64

module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

public section

namespace CFSG.Sporadic.Recognition.HSGraph

theorem ncard_orbit_mul_card_stabilizer (G : Type*) [Group G] {α : Type*} [MulAction G α]
    (x : α) : (MulAction.orbit G x).ncard * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  rw [← MulAction.index_stabilizer, mul_comm]
  exact Subgroup.card_mul_index _

theorem eq_one_of_simple_of_two_lt {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : 2 < Nat.card G) (f : G →* ℤˣ) : f = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with hk | hk
  · have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hk
    have := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at this
    omega
  · ext g
    have : g ∈ f.ker := hk ▸ Subgroup.mem_top g
    simpa using this

theorem false_of_fixed_point_free_aut_hundred {N : Type*} [Group N] [Finite N]
    (hcard : Nat.card N = 100) (φ : MulAut N) (h11 : φ ^ 11 = 1)
    (hfix : ∀ x : N, φ x = x → x = 1) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Fintype N := Fintype.ofFinite N
  obtain ⟨P⟩ : Nonempty (Sylow 5 N) := inferInstance
  have hP : Nat.card P = 25 := by
    rw [Sylow.card_eq_multiplicity, hcard, Nat.factorization_def _ Fact.out,
      show (100 : ℕ) = 5 ^ 2 * 4 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hindex : (P : Subgroup N).index = 4 := by
    have := Subgroup.card_mul_index (P : Subgroup N)
    rw [hP, hcard] at this
    omega
  have hsub : Subsingleton (Sylow 5 N) := by
    have h1 := Sylow.card_dvd_index P
    have h2 := card_sylow_modEq_one 5 N
    rw [hindex] at h1
    have h3 : Nat.card (Sylow 5 N) ≤ 4 := Nat.le_of_dvd (by norm_num) h1
    have h4 : 0 < Nat.card (Sylow 5 N) := Nat.card_pos
    have h5 : Nat.card (Sylow 5 N) = 1 := by
      unfold Nat.ModEq at h2
      interval_cases h : Nat.card (Sylow 5 N) <;> simp_all
    exact (Nat.card_eq_one_iff_unique.1 h5).1
  have hmap : (P : Subgroup N).map φ.toMonoidHom = P :=
    Subgroup.characteristic_iff_map_eq.1 (Sylow.characteristic_of_subsingleton P) φ
  have hφP : ∀ x ∈ (P : Subgroup N), φ x ∈ (P : Subgroup N) := fun x hx => by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom hx
  have hφsymmP : ∀ x ∈ (P : Subgroup N), φ.symm x ∈ (P : Subgroup N) := fun x hx => by
    rw [← hmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have : φ.symm (φ.toMonoidHom y) = y := φ.symm_apply_apply y
    rw [this]
    exact hy
  let σ : Equiv.Perm (P : Subgroup N) :=
    { toFun := fun x => ⟨φ x, hφP x x.2⟩
      invFun := fun x => ⟨φ.symm x, hφsymmP x x.2⟩
      left_inv := fun x => by ext; simp
      right_inv := fun x => by ext; simp }
  have hpow : ∀ (n : ℕ) (x : (P : Subgroup N)),
      (((σ ^ n) x : (P : Subgroup N)) : N) = (φ ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, MulAut.mul_apply]
      rfl
  have hσ : σ ^ 11 ^ 1 = 1 := by
    ext x
    rw [pow_one]
    simp only [Equiv.Perm.coe_one, id_eq]
    rw [hpow, h11]
    rfl
  have hmod := Equiv.Perm.card_compl_support_modEq (σ := σ) hσ
  have hfixed : σ.supportᶜ = {1} := by
    ext x
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · intro hx
      exact Subtype.ext (hfix x (congrArg Subtype.val hx))
    · rintro rfl
      exact Subtype.ext (map_one φ)
  rw [hfixed, Finset.card_singleton, Fintype.card_eq_nat_card, hP] at hmod
  exact absurd hmod (by decide)

end CFSG.Sporadic.Recognition.HSGraph

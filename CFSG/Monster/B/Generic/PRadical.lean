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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.Monster.B.Generic

open Subgroup

theorem le_ker_of_isSimpleGroup {G B : Type*} [Group G] [Group B] [Finite B] (L : Subgroup G)
    [IsSimpleGroup L] {r : ℕ} (hrL : r ∣ Nat.card L) (hrB : ¬ r ∣ Nat.card B) (g : G →* B) :
    L ≤ g.ker := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (g.comp L.subtype).ker with h | h
  · exfalso
    have hinj := (MonoidHom.ker_eq_bot_iff _).mp h
    have hL : Nat.card L = Nat.card (g.comp L.subtype).range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    exact hrB (hrL.trans (hL ▸ card_subgroup_dvd_card _))
  · intro x hx
    have : (⟨x, hx⟩ : L) ∈ (g.comp L.subtype).ker := h ▸ mem_top _
    exact this

theorem eq_bot_of_commutator_top_eq_self {G : Type*} [Group G] [Group.IsNilpotent G]
    (D : Subgroup G) (hD : ⁅D, ⊤⁆ = D) : D = ⊥ := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  have key : ∀ k, D ≤ (⊤ : Subgroup G).lowerCentralSeries k := by
    intro k
    induction k with
    | zero => rw [Subgroup.lowerCentralSeries_zero]; exact le_top
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ, ← hD]
      exact commutator_mono ih le_top
  exact eq_bot_iff.mpr (hn ▸ key n)

theorem p_radical_perfect_action_quotient_test {p r : ℕ} (hp : p.Prime) {P A : Type*}
    [Group P] [Group A] [Finite P] [Finite A] (N : Subgroup P) [N.Normal] (hN : IsPGroup p N)
    (hNP : ⁅N, ⊤⁆ = N) (L : Subgroup (P ⧸ N)) [L.Normal] (hL : IsSimpleGroup L)
    (hrL : r ∣ Nat.card L) (hcard : Nat.card ((P ⧸ N) ⧸ L) ∣ p) (hrA : ¬ r ∣ Nat.card A)
    (f : P →* A) :
    L.comap (QuotientGroup.mk' N) ≤ f.ker ∧ IsCyclic f.range ∧ Nat.card f.range ∣ p ∧
      (commutator P).map f = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  set f' := f.rangeRestrict
  have hf's : Function.Surjective f' := f.rangeRestrict_surjective
  set D := N.map f'
  have hDn : D.Normal := Normal.map inferInstance f' hf's
  let g : P ⧸ N →* f.range ⧸ D := QuotientGroup.map N D f' (le_comap_map f' N)
  have hgs : Function.Surjective g := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨x, rfl⟩ := hf's y
      exact ⟨x, rfl⟩
  have hrB : ¬ r ∣ Nat.card (f.range ⧸ D) := fun h =>
    hrA (h.trans ((card_quotient_dvd_card D).trans (card_subgroup_dvd_card f.range)))
  have hLg := le_ker_of_isSimpleGroup L hrL hrB g
  have hRD : Nat.card (f.range ⧸ D) ∣ p := by
    have h1 : g.ker.index = Nat.card (f.range ⧸ D) := by
      rw [index_ker, MonoidHom.range_eq_top.mpr hgs, card_top]
    rw [← h1]
    exact (index_dvd_of_le hLg).trans (by rwa [index_eq_card])
  have hR : IsPGroup p f.range := by
    obtain ⟨k, hk⟩ := (hN.map f').exists_card_eq
    have hRc := card_eq_card_quotient_mul_card_subgroup D
    rcases (Nat.dvd_prime hp).mp hRD with h | h
    · exact IsPGroup.of_card (n := k) (by rw [hRc, h, one_mul, hk])
    · exact IsPGroup.of_card (n := k + 1) (by rw [hRc, h, hk, pow_succ, mul_comm])
  have hDR : ⁅D, ⊤⁆ = D := by
    rw [← map_top_of_surjective f' hf's, ← map_commutator, hNP]
  have : Group.IsNilpotent f.range := hR.isNilpotent
  have hD : D = ⊥ := eq_bot_of_commutator_top_eq_self D hDR
  have hNf : N ≤ f.ker := by
    intro n hn
    have : f' n ∈ D := mem_map_of_mem f' hn
    rw [hD, mem_bot] at this
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val this
  let fbar : P ⧸ N →* A := QuotientGroup.lift N f hNf
  have hLf := le_ker_of_isSimpleGroup L hrL hrA fbar
  have hkill : L.comap (QuotientGroup.mk' N) ≤ f.ker := by
    intro x hx
    have := hLf hx
    rwa [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.lift_mk] at this
  have hcardR : Nat.card f.range ∣ p := by
    rw [← index_ker]
    refine (index_dvd_of_le hkill).trans ?_
    rw [index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), index_eq_card]
    exact hcard
  have hcyc : IsCyclic f.range := by
    rcases (Nat.dvd_prime hp).mp hcardR with h | h
    · have : Subsingleton f.range := (Nat.card_eq_one_iff_unique.mp h).1
      exact isCyclic_of_subsingleton
    · have : Fact (Nat.card f.range).Prime := ⟨h ▸ hp⟩
      exact isCyclic_of_prime_card rfl
  refine ⟨hkill, hcyc, hcardR, ?_⟩
  have hcomm := IsCyclic.isMulCommutative (α := f.range)
  rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
    commutator_eq_bot_iff_le_centralizer]
  intro x hx y hy
  have := hcomm.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩
  exact congrArg Subtype.val this

end CFSG.Monster.B.Generic

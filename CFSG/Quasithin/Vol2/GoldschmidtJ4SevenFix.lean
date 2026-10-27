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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.Quasithin.H13.Seven

open MulAction Subgroup

theorem exists_fixed_in_invariant {G Ω : Type*} [Group G] [MulAction G Ω] (g : G) {a : ℕ}
    (hg : g ^ 2 ^ a = 1) (Φ : Set Ω) (hΦ : ∀ p, p ∈ Φ ↔ g • p ∈ Φ) (hfin : Φ.Finite)
    (hodd : Odd Φ.ncard) : ∃ p ∈ Φ, g • p = p := by
  classical
  have : Finite Φ := hfin
  have : Fintype Φ := Fintype.ofFinite Φ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ : Equiv.Perm Φ := (MulAction.toPerm g).subtypePerm (fun p => (hΦ p).symm)
  have hpow : ∀ (n : ℕ) (p : Φ), (((σ ^ n) p : Φ) : Ω) = (g ^ n) • (p : Ω) := by
    intro n
    induction n with
    | zero => intro p; simp
    | succ n ih =>
      intro p
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, mul_smul]
      rfl
  have hσ : σ ^ 2 ^ a = 1 := by
    refine Equiv.ext fun p => Subtype.ext ?_
    rw [hpow, hg, one_smul]
    rfl
  have h := Equiv.Perm.card_compl_support_modEq hσ
  have hcard : Fintype.card Φ = Φ.ncard := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [hcard] at h
  by_contra! hne
  have h0 : (σ.supportᶜ).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro p hp
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hp
    have hv := congrArg Subtype.val hp
    exact hne p p.2 hv
  rw [h0] at h
  have h2 : Φ.ncard % 2 = 0 := (Nat.ModEq.symm h)
  rcases hodd with ⟨k, hk⟩
  omega

theorem conj_pow_odd {G : Type*} [Group G] {y g : G} (hg : g * y * g⁻¹ = y⁻¹) {o : ℕ}
    (ho : Odd o) : g ^ o * y * (g ^ o)⁻¹ = y⁻¹ := by
  obtain ⟨k, rfl⟩ := ho
  have h1 : g * y⁻¹ * g⁻¹ = y := by
    have := congrArg (fun z => z⁻¹) hg
    simpa [mul_assoc] using this
  have h2 : g ^ 2 * y = y * g ^ 2 := by
    have : g * (g * y * g⁻¹) * g⁻¹ = g * y⁻¹ * g⁻¹ := by rw [hg]
    rw [h1] at this
    rw [pow_two]
    calc g * g * y = (g * (g * y * g⁻¹) * g⁻¹) * (g * g) := by group
      _ = y * (g * g) := by rw [this]
  have h3 : Commute (g ^ 2) y := h2
  have h4 : Commute ((g ^ 2) ^ k) y⁻¹ := (h3.pow_left k).inv_right
  calc g ^ (2 * k + 1) * y * (g ^ (2 * k + 1))⁻¹
      = (g ^ 2) ^ k * (g * y * g⁻¹) * ((g ^ 2) ^ k)⁻¹ := by group
    _ = y⁻¹ := by rw [hg, h4.eq]; group

theorem not_real_of_odd_fixed {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] (w₀ : Ω)
    (hH : ∀ y g : G, y • w₀ = w₀ → g • w₀ = w₀ → orderOf y = 7 → g * y * g⁻¹ ≠ y⁻¹)
    {y : G} (hy : orderOf y = 7)
    (hfin : {p : Ω | (∃ j : G, j • w₀ = p) ∧ y • p = p}.Finite)
    (hodd : Odd {p : Ω | (∃ j : G, j • w₀ = p) ∧ y • p = p}.ncard) (g : G) :
    g * y * g⁻¹ ≠ y⁻¹ := by
  intro hg
  set Φ : Set Ω := {p : Ω | (∃ j : G, j • w₀ = p) ∧ y • p = p} with hΦ
  obtain ⟨a, o, ho, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  set g' : G := g ^ o with hg'
  have hg'2 : g' ^ 2 ^ a = 1 := by
    rw [hg', ← pow_mul, mul_comm, ← hn]
    exact pow_orderOf_eq_one g
  have hg'inv : g' * y * g'⁻¹ = y⁻¹ := conj_pow_odd hg ho
  have hstab : ∀ h : G, h * y * h⁻¹ = y⁻¹ → ∀ p ∈ Φ, h • p ∈ Φ := by
    intro h hh p ⟨⟨j, hj⟩, hp⟩
    refine ⟨⟨h * j, by rw [mul_smul, hj]⟩, ?_⟩
    have hy' : h⁻¹ * y * h = y⁻¹ := by
      have : y = h⁻¹ * y⁻¹ * h := by
        calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
          _ = h⁻¹ * y⁻¹ * h := by rw [hh]
      have := congrArg (fun z => z⁻¹) this
      simpa [mul_assoc] using this.symm
    calc y • (h • p) = h • ((h⁻¹ * y * h) • p) := by
          rw [← mul_smul, ← mul_smul]; congr 1; group
      _ = h • p := by
          rw [hy', inv_smul_eq_iff.2 hp.symm]
  have hinvg : g'⁻¹ * y * g'⁻¹⁻¹ = y⁻¹ := by
    have : g'⁻¹ * y * g' = y⁻¹ := by
      have h1 : y = g'⁻¹ * y⁻¹ * g' := by
        calc y = g'⁻¹ * (g' * y * g'⁻¹) * g' := by group
          _ = g'⁻¹ * y⁻¹ * g' := by rw [hg'inv]
      have := congrArg (fun z => z⁻¹) h1
      simpa [mul_assoc] using this.symm
    simpa using this
  have hiff : ∀ p, p ∈ Φ ↔ g' • p ∈ Φ := by
    intro p
    refine ⟨hstab g' hg'inv p, fun hp => ?_⟩
    have := hstab g'⁻¹ hinvg _ hp
    rwa [inv_smul_smul] at this
  obtain ⟨p, ⟨⟨j, hj⟩, hpy⟩, hpg⟩ := exists_fixed_in_invariant g' hg'2 Φ hiff hfin hodd
  refine hH (j⁻¹ * y * j) (j⁻¹ * g' * j) ?_ ?_ ?_ ?_
  · rw [mul_smul, mul_smul, hj, hpy, inv_smul_eq_iff, hj]
  · rw [mul_smul, mul_smul, hj, hpg, inv_smul_eq_iff, hj]
  · rw [show j⁻¹ * y * j = (MulAut.conj j⁻¹).toMonoidHom y by simp,
      orderOf_injective _ (MulAut.conj j⁻¹).injective, hy]
  · calc j⁻¹ * g' * j * (j⁻¹ * y * j) * (j⁻¹ * g' * j)⁻¹ = j⁻¹ * (g' * y * g'⁻¹) * j := by group
      _ = (j⁻¹ * y * j)⁻¹ := by rw [hg'inv]; group

end CFSG.Quasithin.H13.Seven

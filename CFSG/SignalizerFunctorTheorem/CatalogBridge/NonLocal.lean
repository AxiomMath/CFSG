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
public import Mathlib.Data.Int.Star
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

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

@[expose] def NonLocalized {X : Type*} [Group X] (C : Subgroup X) : Prop :=
  ∀ T : Subgroup X, T ≠ ⊥ → Group.IsSolvable T → ¬ C ≤ Subgroup.normalizer (T : Set X)

theorem NonLocalized.mono {X : Type*} [Group X] {C C' : Subgroup X} (h : C ≤ C')
    (hC : NonLocalized C) : NonLocalized C' := fun T hT hs hle => hC T hT hs (h.trans hle)

theorem exists_abelian_normalized {X : Type*} [Group X] {T : Subgroup X} (hT : T ≠ ⊥)
    (hs : Group.IsSolvable T) :
    ∃ A : Subgroup X, A ≠ ⊥ ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      ∀ g ∈ Subgroup.normalizer (T : Set X), ∀ x ∈ A, g * x * g⁻¹ ∈ A := by
  classical
  have hex : ∃ n, derivedSeries T n = ⊥ := hs.solvable
  have hm : derivedSeries T (Nat.find hex) = ⊥ := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, derivedSeries_zero] at hm
    apply hT
    ext x
    simp only [Subgroup.mem_bot]
    constructor
    · intro hx
      have : (⟨x, hx⟩ : T) ∈ (⊤ : Subgroup T) := Subgroup.mem_top _
      rw [hm, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · rintro rfl
      exact T.one_mem
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hkne : derivedSeries T k ≠ ⊥ := Nat.find_min hex (by omega)
  have hk1 : derivedSeries T (k + 1) = ⊥ := by
    rw [hk] at hm
    exact hm
  refine ⟨(derivedSeries T k).map T.subtype, ?_, ?_, ?_⟩
  · intro hbot
    exact hkne ((Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective).mp hbot)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hc : ⁅a, b⁆ ∈ derivedSeries T (k + 1) := by
      rw [derivedSeries_succ]
      exact Subgroup.commutator_mem_commutator ha hb
    rw [hk1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact congrArg Subtype.val hc
  · intro g hg x hx
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨(T.normalizerMonoidHom ⟨g, hg⟩ : MulAut T) a, ?_, ?_⟩
    · have := map_derivedSeries_le_derivedSeries
        ((T.normalizerMonoidHom ⟨g, hg⟩ : MulAut T).toMonoidHom) k
        (Subgroup.mem_map_of_mem _ ha)
      exact this
    · simp [Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem nonLocalized_of_elemAbelian {X : Type*} [Group X] [Finite X] {C : Subgroup X}
    (h : ∀ (s : ℕ) (E : Subgroup X), s.Prime → E ≠ ⊥ → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      (∀ x ∈ E, x ^ s = 1) → ¬ C ≤ Subgroup.normalizer (E : Set X)) : NonLocalized C := by
  intro T hT hs hle
  obtain ⟨A, hA0, hAcomm, hAnorm⟩ := exists_abelian_normalized hT hs
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hA0 (Subgroup.eq_bot_iff_forall A |>.mpr hcon)
  have hord : orderOf a ≠ 1 := fun h1 => ha1 (orderOf_eq_one_iff.mp h1)
  obtain ⟨s, hsp, hsd⟩ := Nat.exists_prime_and_dvd hord
  obtain ⟨t, ht⟩ := hsd
  have hpos : 0 < orderOf a := orderOf_pos a
  let E : Subgroup X :=
    { carrier := {x | x ∈ A ∧ x ^ s = 1}
      mul_mem' := fun {x y} hx hy => by
        refine ⟨A.mul_mem hx.1 hy.1, ?_⟩
        rw [(show Commute x y from hAcomm x hx.1 y hy.1).mul_pow, hx.2, hy.2, one_mul]
      one_mem' := ⟨A.one_mem, one_pow s⟩
      inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hbmem : a ^ t ∈ E := by
    refine ⟨A.pow_mem haA t, ?_⟩
    rw [← pow_mul, mul_comm, ← ht]
    exact pow_orderOf_eq_one a
  have hb1 : a ^ t ≠ 1 := by
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [ht] at h2
    have ht0 : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [ht, h0, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact h0
    have := Nat.le_of_dvd ht0 h2
    have := hsp.two_le
    nlinarith
  have hE0 : E ≠ ⊥ := fun hbot => hb1 ((Subgroup.mem_bot.mp (hbot ▸ hbmem)))
  have hnorm : ∀ g ∈ C, ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    intro g hg x hx
    refine ⟨hAnorm g (hle hg) x hx.1, ?_⟩
    rw [conj_pow, hx.2]
    simp
  refine h s E hsp hE0 (fun x hx y hy => hAcomm x hx.1 y hy.1) (fun x hx => hx.2) fun g hg => ?_
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hnorm g hg x hx, fun hx => ?_⟩
  have := hnorm g⁻¹ (C.inv_mem hg) _ hx
  simpa [mul_assoc] using this

end CFSG.SignalizerFunctorTheorem.CatalogBridge

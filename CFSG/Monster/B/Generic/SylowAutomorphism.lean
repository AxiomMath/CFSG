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

open Subgroup MulAction
open scoped Pointwise

@[expose] noncomputable def mulAutRestrict {T : Type*} [Group T] (σ : MulAut T) (P : Subgroup T)
    (h : P.map σ.toMonoidHom = P) : MulAut P :=
  (σ.subgroupMap P).trans (MulEquiv.subgroupCongr h)

theorem mulAutRestrict_apply {T : Type*} [Group T] (σ : MulAut T) (P : Subgroup T)
    (h : P.map σ.toMonoidHom = P) (x : P) : (mulAutRestrict σ P h x : T) = σ x :=
  rfl

theorem mulAutRestrict_pow_apply {T : Type*} [Group T] (σ : MulAut T) (P : Subgroup T)
    (h : P.map σ.toMonoidHom = P) (n : ℕ) (x : P) :
    (((mulAutRestrict σ P h) ^ n) x : T) = (σ ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, mulAutRestrict_apply, ih, pow_succ', MulAut.mul_apply]

private theorem eq_one_of_dvd_of_coprime {n m : ℕ} (hn : n ∣ m)
    (h : ∀ q : ℕ, q.Prime → q ∣ m → ¬ q ∣ n) : n = 1 := by
  by_contra hn1
  obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd hn1
  exact h q hq (hqn.trans hn) hqn

theorem coprime_sylow_automorphism_prime_test {T : Type*} [Group T] [Finite T] {r : ℕ}
    (hr : r.Prime) (hrT : ¬ r ∣ Nat.card T)
    (hSyl : ∀ p : ℕ, p.Prime → p ∣ Nat.card T → ∃ P : Sylow p T, ¬ r ∣ Nat.card (MulAut P)) :
    ¬ r ∣ Nat.card (MulAut T) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Finite (MulAut T) :=
    Finite.of_injective (fun σ : MulAut T => (σ : T → T)) fun σ τ h => MulEquiv.ext
      (congrFun h)
  intro hdvd
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hZ : IsPGroup r (zpowers σ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσ, pow_one])
  have hfix : ∀ p : ℕ, p.Prime → p ∣ Nat.card T →
      ∃ P : Sylow p T, ∀ x ∈ (P : Subgroup T), σ x = x := by
    intro p hp hpT
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨P₀, hP₀⟩ := hSyl p hp hpT
    have hmod := hZ.card_modEq_card_fixedPoints (Sylow p T)
    have hnr : ¬ r ∣ Nat.card (Sylow p T) := fun h =>
      hrT (h.trans (by rw [Sylow.card_eq_index_normalizer P₀]; exact index_dvd_card _))
    have hne : (fixedPoints (zpowers σ) (Sylow p T)).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro he
      have h0 : Nat.card (∅ : Set (Sylow p T)) = 0 := by simp
      rw [he, h0] at hmod
      exact hnr (Nat.modEq_zero_iff_dvd.mp hmod)
    obtain ⟨P, hP⟩ := hne
    have hσP' : σ • (P : Subgroup T) = P := by
      have := congrArg (fun Q : Sylow p T => (Q : Subgroup T)) (hP ⟨σ, mem_zpowers σ⟩)
      simpa [Sylow.pointwise_smul_def] using this
    have hσP : (P : Subgroup T).map σ.toMonoidHom = P := by
      ext x
      rw [mem_map_equiv]
      conv_rhs => rw [← hσP']
      rw [mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    obtain ⟨g, hg⟩ := exists_smul_eq T P₀ P
    have hcard : Nat.card (MulAut P) = Nat.card (MulAut P₀) := by
      subst hg
      exact Nat.card_congr (MulAut.congr (P₀.equivSMul g)).toEquiv.symm
    let τ := mulAutRestrict σ P hσP
    have hτr : τ ^ r = 1 := by
      ext x
      rw [mulAutRestrict_pow_apply, ← hσ, pow_orderOf_eq_one]
      rfl
    have hτ : τ = 1 := by
      have h1 : orderOf τ ∣ r := orderOf_dvd_of_pow_eq_one hτr
      have h2 : orderOf τ ∣ Nat.card (MulAut P) := orderOf_dvd_natCard τ
      rcases (Nat.dvd_prime hr).mp h1 with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact absurd (h ▸ h2) (hcard ▸ hP₀)
    refine ⟨P, fun x hx => ?_⟩
    have := congrArg (fun φ : MulAut P => (φ ⟨x, hx⟩ : T)) hτ
    simpa [τ, mulAutRestrict_apply] using this
  let C : Subgroup T :=
    { carrier := {x | σ x = x}
      mul_mem' := fun {a b} (ha : σ a = a) (hb : σ b = b) =>
        show σ (a * b) = a * b by rw [map_mul, ha, hb]
      one_mem' := map_one σ
      inv_mem' := fun {a} (ha : σ a = a) => show σ a⁻¹ = a⁻¹ by rw [map_inv, ha] }
  have hC : C.index = 1 := by
    refine eq_one_of_dvd_of_coprime (index_dvd_card C) fun q hq hqT => ?_
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨P, hP⟩ := hfix q hq hqT
    exact fun h => P.not_dvd_index (h.trans (index_dvd_of_le hP))
  have hσ1 : σ = 1 := by
    ext x
    have : x ∈ C := (index_eq_one.mp hC) ▸ mem_top x
    exact this
  rw [hσ1, orderOf_one] at hσ
  exact hr.one_lt.ne hσ

theorem not_dvd_card_mulAut_of_not_modEq {P : Type*} [Group P] [Finite P] {p r k : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hP : Nat.card P = p ^ k)
    (h : ∀ j < k, ¬ p ^ k ≡ p ^ j [MOD r]) : ¬ r ∣ Nat.card (MulAut P) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Finite (MulAut P) :=
    Finite.of_injective (fun σ : MulAut P => (σ : P → P)) fun σ τ h => MulEquiv.ext
      (congrFun h)
  intro hdvd
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hZ : IsPGroup r (zpowers τ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hτ, pow_one])
  have hmod := hZ.card_modEq_card_fixedPoints P
  have hF : Nat.card (fixedPoints (zpowers τ) P) =
      Nat.card (FixedPoints.subgroup (zpowers τ) P) := rfl
  obtain ⟨j, hj, hFj⟩ := (Nat.dvd_prime_pow hp).mp
    (hP ▸ (FixedPoints.subgroup (zpowers τ) P).card_subgroup_dvd_card)
  rw [hP, hF, hFj] at hmod
  rcases hj.lt_or_eq with hjk | rfl
  · exact h j hjk hmod
  · apply hr.one_lt.ne
    rw [← hτ, eq_comm, orderOf_eq_one_iff]
    have htop : FixedPoints.subgroup (zpowers τ) P = ⊤ :=
      (card_eq_iff_eq_top _).mp (hFj.trans hP.symm)
    ext x
    have hx : x ∈ FixedPoints.subgroup (zpowers τ) P := htop ▸ mem_top x
    have := (FixedPoints.mem_subgroup (zpowers τ) P x).mp hx ⟨τ, mem_zpowers τ⟩
    simpa [Subgroup.mk_smul, MulAut.smul_def] using this

theorem not_eleven_dvd_card_mulAut :
    3968055 = 3 ^ 3 * 5 * 7 * 13 * 17 * 19 ∧
      ∀ (T : Type*) [Group T] [Finite T], Nat.card T ∣ 3968055 → ¬ 11 ∣ Nat.card (MulAut T) := by
  refine ⟨by norm_num, fun T _ _ hT => ?_⟩
  have h11 : Nat.Prime 11 := by norm_num
  refine coprime_sylow_automorphism_prime_test h11 (fun h => absurd (h.trans hT) (by norm_num))
    fun p hp hpT => ?_
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p T))
  refine ⟨P, ?_⟩
  obtain ⟨k, hk⟩ := (P.isPGroup').exists_card_eq
  have hkdvd : p ^ k ∣ 3968055 := hk ▸ (card_subgroup_dvd_card (P : Subgroup T)).trans hT
  have hp' : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 ∨ p = 19 := by
    have hpd : p ∣ 3 ^ 3 * 5 * 7 * 13 * 17 * 19 := hpT.trans hT
    have pe : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h =>
      (Nat.prime_dvd_prime_iff_eq hp hq).mp h
    rcases hp.dvd_mul.mp hpd with h | h
    · rcases hp.dvd_mul.mp h with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · rcases hp.dvd_mul.mp h with h | h
            · exact Or.inl (pe 3 Nat.prime_three (hp.dvd_of_dvd_pow h))
            · exact Or.inr (Or.inl (pe 5 (by norm_num) h))
          · exact Or.inr (Or.inr (Or.inl (pe 7 (by norm_num) h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (pe 13 (by norm_num) h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (pe 17 (by norm_num) h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pe 19 (by norm_num) h)))))
  refine not_dvd_card_mulAut_of_not_modEq hp h11 hk fun j hj hmod => ?_
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl
  · have hk3 : k ≤ 3 := by
      by_contra hk4
      exact absurd ((Nat.pow_dvd_pow 3 (by omega : 4 ≤ k)).trans hkdvd) (by norm_num)
    interval_cases k <;> interval_cases j <;> exact absurd hmod (by decide)
  all_goals
    have hk1 : k ≤ 1 := by
      by_contra hk2
      exact absurd ((Nat.pow_dvd_pow _ (by omega : 2 ≤ k)).trans hkdvd) (by norm_num)
    obtain rfl : k = 1 := by omega
    obtain rfl : j = 0 := by omega
    exact absurd hmod (by decide)

end CFSG.Monster.B.Generic

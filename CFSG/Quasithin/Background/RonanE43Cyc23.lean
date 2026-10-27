module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Quasithin

theorem exists_fixed_mem_of_pow {M : Type*} [CommGroup M] (a : MulAut M) (ha : a ^ 23 = 1)
    (D E : Subgroup M) (hD : ∀ d ∈ D, a d ∈ D) (hE : ∀ e ∈ E, a e ∈ E) {x : M} (hx2 : x * x = 1)
    (hxE : x ∈ E) (hxD : a x * x⁻¹ ∈ D) : ∃ u ∈ E, a u = u ∧ u * x⁻¹ ∈ D := by
  have hpowD : ∀ i : ℕ, (a ^ i) x * x⁻¹ ∈ D := by
    intro i
    induction i with
    | zero => simp [Subgroup.one_mem]
    | succ i ih =>
      have h1 : a ((a ^ i) x * x⁻¹) ∈ D := hD _ ih
      have h2 : (a ^ (i + 1)) x * x⁻¹ = a ((a ^ i) x * x⁻¹) * (a x * x⁻¹) := by
        rw [pow_succ', MulAut.mul_apply, map_mul, map_inv]
        group
      rw [h2]
      exact D.mul_mem h1 hxD
  have hpowE : ∀ i : ℕ, (a ^ i) x ∈ E := by
    intro i
    induction i with
    | zero => simpa using hxE
    | succ i ih =>
      rw [pow_succ', MulAut.mul_apply]
      exact hE _ ih
  refine ⟨∏ i ∈ Finset.range 23, (a ^ i) x, Subgroup.prod_mem E fun i _ => hpowE i, ?_, ?_⟩
  · rw [map_prod]
    have h1 : ∀ i ∈ Finset.range 23, a ((a ^ i) x) = (a ^ (i + 1)) x := by
      intro i _
      rw [pow_succ', MulAut.mul_apply]
    rw [Finset.prod_congr rfl h1]
    have h2 := Finset.prod_range_succ' (fun i => (a ^ i) x) 23
    have h3 := Finset.prod_range_succ (fun i => (a ^ i) x) 23
    have h4 : (a ^ 23) x = (a ^ 0) x := by rw [ha]; simp
    rw [h3, h4] at h2
    exact (mul_right_cancel h2).symm
  · have hprod : ∏ i ∈ Finset.range 23, ((a ^ i) x * x⁻¹) ∈ D :=
      Subgroup.prod_mem D fun i _ => hpowD i
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hprod
    have hxi : x⁻¹ * x⁻¹ = 1 := by
      rw [← mul_inv_rev, hx2, inv_one]
    have h23 : (x⁻¹) ^ 23 = x⁻¹ := by
      have : (x⁻¹) ^ 2 = 1 := by rw [pow_two, hxi]
      calc (x⁻¹) ^ 23 = ((x⁻¹) ^ 2) ^ 11 * x⁻¹ := by rw [← pow_mul, ← pow_succ]
        _ = x⁻¹ := by rw [this, one_pow, one_mul]
    rw [h23] at hprod
    exact hprod

theorem permMod_mul_self (n : ℕ) (x : G6.PermMod n) : x * x = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
  generalize Multiplicative.toAdd x i = z
  revert z
  decide

theorem eq_one_or_allOnes_of_perm23 {σ : Equiv.Perm (Fin 24)} (hσ : orderOf σ = 23)
    {u : G6.PermMod 24} (hu : u ∈ G6.coreMod 24) (hσu : G6.permAct 24 σ u = u) :
    u = 1 ∨ u = G6.allOnes 24 := by
  have hcyc : σ.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by rw [hσ]; norm_num) (by rw [hσ, Fintype.card_fin]; norm_num)
  have hcard : σ.support.card = 23 := by rw [← hcyc.orderOf, hσ]
  have hcompl : σ.supportᶜ.card = 1 := by
    rw [Finset.card_compl, hcard, Fintype.card_fin]
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcompl
  have hpfix : σ p = p := by
    have : p ∈ σ.supportᶜ := by rw [hp]; simp
    simpa [Equiv.Perm.mem_support] using this
  have hq : ∀ q, q ≠ p → σ q ≠ q := by
    intro q hqp hfix
    have : q ∈ σ.supportᶜ := by simpa [Equiv.Perm.mem_support] using hfix
    rw [hp] at this
    exact hqp (by simpa using this)
  have hinv : ∀ i, Multiplicative.toAdd u (σ⁻¹ i) = Multiplicative.toAdd u i := fun i => by
    have := congrArg (fun v : G6.PermMod 24 => Multiplicative.toAdd v i) hσu
    simpa [G6.permAct_apply] using this
  have hinv' : ∀ i, Multiplicative.toAdd u (σ i) = Multiplicative.toAdd u i := fun i => by
    have := hinv (σ i)
    simpa using this.symm
  have hinvk : ∀ (k : ℕ) i, Multiplicative.toAdd u ((σ ^ k) i) = Multiplicative.toAdd u i := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      rw [pow_succ, Equiv.Perm.mul_apply, ih, hinv']
  obtain ⟨q₀, hq₀⟩ := exists_ne p
  set a := Multiplicative.toAdd u q₀ with ha
  set b := Multiplicative.toAdd u p with hb
  have hconst : ∀ i, i ≠ p → Multiplicative.toAdd u i = a := by
    intro i hi
    obtain ⟨k, hk⟩ := hcyc.exists_pow_eq (hq q₀ hq₀) (hq i hi)
    rw [← hk, hinvk]
  have hsum : ∑ i, Multiplicative.toAdd u i = 24 • a + (b - a) := by
    have h1 : ∀ i, Multiplicative.toAdd u i = a + (if i = p then b - a else 0) := by
      intro i
      by_cases hi : i = p
      · rw [if_pos hi, hi]
        show b = a + (b - a)
        ring
      · simp [hi, hconst i hi]
    simp_rw [h1]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
  have hzero : ∑ i, Multiplicative.toAdd u i = 0 := hu
  have h24 : (24 : ℕ) • a = 0 := (by decide : ∀ z : ZMod 2, (24 : ℕ) • z = 0) a
  rw [h24, zero_add] at hsum
  have hba : b = a := by
    rw [hsum] at hzero
    exact sub_eq_zero.mp hzero
  have hall : ∀ i, Multiplicative.toAdd u i = a := by
    intro i
    by_cases hi : i = p
    · rw [hi]; exact hba
    · exact hconst i hi
  have hcases : a = 0 ∨ a = 1 := (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) a
  rcases hcases with h0 | h1
  · left
    apply Multiplicative.toAdd.injective
    funext i
    rw [hall, h0]
    rfl
  · right
    apply Multiplicative.toAdd.injective
    funext i
    rw [hall, h1]
    rfl

end CFSG.Quasithin.RonanE43

module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K47a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup

section One

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem mul_mod_inv_uc6 {r j j' a : ℕ} (hr : 1 < r) (hj' : j * j' % r = 1) (ha : a < r) :
    a * j % r * j' % r = a := by
  have hjj : j * j' ≡ 1 [MOD r] := by
    unfold Nat.ModEq
    rw [hj', Nat.mod_eq_of_lt hr]
  have h1 : a * j % r * j' ≡ a * j * j' [MOD r] := (Nat.mod_modEq (a * j) r).mul_right j'
  have h2 : a * j * j' ≡ a * 1 [MOD r] := by
    rw [mul_assoc]
    exact hjj.mul_left a
  have h3 : a * j % r * j' ≡ a [MOD r] := by simpa using h1.trans h2
  unfold Nat.ModEq at h3
  rw [h3, Nat.mod_eq_of_lt ha]

theorem sum_pow_mul_eq_uc6 (f : Module.End (ZMod 2) V) {r : ℕ} (hr : r.Prime) (hfr : f ^ r = 1)
    {j : ℕ} (hj0 : 0 < j) (hjr : j < r) :
    ∑ i ∈ Finset.range r, f ^ (i * j) = ∑ i ∈ Finset.range r, f ^ i := by
  obtain ⟨j', hj'r, hj'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hr).2 (Nat.not_dvd_of_pos_of_lt hj0 hjr)))
    hr.one_lt
  refine Finset.sum_nbij' (fun a => a * j % r) (fun b => b * j' % r) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_range.2 (Nat.mod_lt _ hr.pos)
  · intro b _
    exact Finset.mem_range.2 (Nat.mod_lt _ hr.pos)
  · intro a ha
    exact mul_mod_inv_uc6 hr.one_lt hj' (Finset.mem_range.1 ha)
  · intro b hb
    have hj'' : j' * j % r = 1 := by rw [mul_comm]; exact hj'
    exact mul_mod_inv_uc6 hr.one_lt hj'' (Finset.mem_range.1 hb)
  · intro a _
    exact pow_eq_pow_mod (a * j) hfr

theorem double_sum_uc6 (f g : Module.End (ZMod 2) V) (hfg : f * g = g * f) {r : ℕ} (hr : r.Prime)
    (hfr : f ^ r = 1) :
    ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r, (f ^ i * g) ^ j =
      r • (1 : Module.End (ZMod 2) V) +
        (∑ k ∈ Finset.range r, f ^ k) * (∑ j ∈ Finset.range r, g ^ j - 1) := by
  have hcomm : ∀ i : ℕ, Commute (f ^ i) g := fun i =>
    Commute.pow_left (show Commute f g from hfg) i
  have h1 : ∀ i j : ℕ, (f ^ i * g) ^ j = f ^ (i * j) * g ^ j := fun i j => by
    rw [(hcomm i).mul_pow, pow_mul]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ j ∈ Finset.range r, ∑ i ∈ Finset.range r, f ^ (i * j) * g ^ j =
      (∑ i ∈ Finset.range r, f ^ (i * j)) * g ^ j := fun j _ => by rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl h2]
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := hr.pos; omega⟩
  rw [Finset.sum_range_succ' (fun j => (∑ i ∈ Finset.range (r' + 1), f ^ (i * j)) * g ^ j),
    Finset.sum_range_succ' (fun j => g ^ j)]
  simp only [mul_zero, pow_zero, mul_one, Finset.sum_const, Finset.card_range, add_sub_cancel_right]
  rw [Finset.mul_sum, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [sum_pow_mul_eq_uc6 f hr hfr (Nat.succ_pos j) (by have := Finset.mem_range.1 hj; omega)]

theorem conj_pow_uc6 {M : Type*} [Monoid M] (u u' x : M) (hu : u * u' = 1) (hu' : u' * u = 1)
    (j : ℕ) : (u * x * u') ^ j = u * x ^ j * u' := by
  induction j with
  | zero => simp [hu]
  | succ j ih =>
    calc (u * x * u') ^ (j + 1) = (u * x * u') ^ j * (u * x * u') := pow_succ _ _
      _ = u * x ^ j * (u' * u) * x * u' := by rw [ih]; simp only [mul_assoc]
      _ = u * x ^ (j + 1) * u' := by rw [hu', mul_one, pow_succ]; simp only [mul_assoc]

theorem op47_one_uc6 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (f g P P' : Module.End (ZMod 2) V)
    (hfg : f * g = g * f) (hPf : P * f = f * P) (hPP' : P * P' = 1) (hP'P : P' * P = 1)
    (hPg : P * g * P' = f * g) (hfr : f ^ r = 1) (hgr : g ^ r = 1)
    (hC : ∀ a b : V, a ≠ 0 → b ≠ 0 → g a = a → g b = b → a = b) : f = 1 := by
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  have hfinj : ∀ a, f a = 0 → a = 0 := by
    intro a ha
    obtain ⟨r', hr'⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := hr.pos; omega⟩
    have h1 : (f ^ r) a = a := by rw [hfr]; rfl
    rw [hr', pow_succ, Module.End.mul_apply, ha, map_zero] at h1
    exact h1.symm
  have hffix : ∀ a, g a = a → f a = a := by
    intro a ha
    by_cases ha0 : a = 0
    · rw [ha0, map_zero]
    · have hfa0 : f a ≠ 0 := fun h => ha0 (hfinj a h)
      have hgfa : g (f a) = f a := by
        have := congrArg (fun h : Module.End (ZMod 2) V => h a) hfg
        simp only [Module.End.mul_apply] at this
        rw [← this, ha]
      exact hC _ _ hfa0 ha0 hgfa ha
  have hPfc : Commute P f := hPf
  have hPi_f : ∀ i : ℕ, P ^ i * f = f * P ^ i := fun i => (Commute.pow_left hPfc i).eq
  have hQQ : ∀ i : ℕ, P ^ i * P' ^ i = 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc P ^ (i + 1) * P' ^ (i + 1) = P * (P ^ i * P' ^ i) * P' := by
            rw [pow_succ' P i, pow_succ P' i]; simp only [mul_assoc]
        _ = 1 := by rw [ih, mul_one, hPP']
  have hQ'Q : ∀ i : ℕ, P' ^ i * P ^ i = 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc P' ^ (i + 1) * P ^ (i + 1) = P' ^ i * (P' * P) * P ^ i := by
            rw [pow_succ P' i, pow_succ' P i]; simp only [mul_assoc]
        _ = 1 := by rw [hP'P, mul_one, ih]
  have hPf_pow : ∀ i : ℕ, P * f ^ i = f ^ i * P := fun i =>
    (Commute.pow_right hPfc i).eq
  have hPi : ∀ i : ℕ, P ^ i * g * P' ^ i = f ^ i * g := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc P ^ (i + 1) * g * P' ^ (i + 1) = P * (P ^ i * g * P' ^ i) * P' := by
            rw [pow_succ' P i, pow_succ P' i]; simp only [mul_assoc]
        _ = P * (f ^ i * g) * P' := by rw [ih]
        _ = f ^ i * (P * g * P') := by
            calc P * (f ^ i * g) * P' = (P * f ^ i) * g * P' := by simp only [mul_assoc]
              _ = (f ^ i * P) * g * P' := by rw [hPf_pow i]
              _ = f ^ i * (P * g * P') := by simp only [mul_assoc]
        _ = f ^ i * (f * g) := by rw [hPg]
        _ = f ^ (i + 1) * g := by rw [pow_succ, mul_assoc]
  have hNi : ∀ i : ℕ, ∑ j ∈ Finset.range r, (f ^ i * g) ^ j =
      P ^ i * (∑ j ∈ Finset.range r, g ^ j) * P' ^ i := by
    intro i
    have hj : ∀ j : ℕ, (f ^ i * g) ^ j = P ^ i * g ^ j * P' ^ i := by
      intro j
      rw [← hPi i]
      exact conj_pow_uc6 (P ^ i) (P' ^ i) g (hQQ i) (hQ'Q i) j
    simp only [hj, Finset.mul_sum, Finset.sum_mul]
  have hSf : (∑ k ∈ Finset.range r, f ^ k) * (f - 1) = 0 := by
    rw [geom_sum_mul, hfr, sub_self]
  have hNgfix : ∀ y, g ((∑ j ∈ Finset.range r, g ^ j) y) = (∑ j ∈ Finset.range r, g ^ j) y := by
    intro y
    have := congrArg (fun h : Module.End (ZMod 2) V => h y) (T_mul_sum_uc6 g r hgr)
    simpa using this
  have hcommSN : (∑ k ∈ Finset.range r, f ^ k) * (∑ j ∈ Finset.range r, g ^ j) =
      (∑ j ∈ Finset.range r, g ^ j) * (∑ k ∈ Finset.range r, f ^ k) :=
    Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun j _ =>
      Commute.pow_pow (show Commute f g from hfg) k j
  have hz : ∀ x, (f - 1) x = 0 := by
    intro x
    obtain ⟨w, hw⟩ : ∃ w, w = (f - 1) x := ⟨_, rfl⟩
    have hSw : (∑ k ∈ Finset.range r, f ^ k) w = 0 := by
      rw [hw]
      have := congrArg (fun h : Module.End (ZMod 2) V => h x) hSf
      simpa using this
    have hop : ∑ i ∈ Finset.range r, (P ^ i * (∑ j ∈ Finset.range r, g ^ j) * P' ^ i) =
        r • (1 : Module.End (ZMod 2) V) + (∑ k ∈ Finset.range r, f ^ k) *
          (∑ j ∈ Finset.range r, g ^ j - 1) := by
      rw [← double_sum_uc6 f g hfg hr hfr]
      exact Finset.sum_congr rfl fun i _ => (hNi i).symm
    have hr1 : (r • (1 : Module.End (ZMod 2) V)) w = w := by
      rw [odd_nsmul_end_uc6 hrodd]
      rfl
    have hcn : (∑ k ∈ Finset.range r, f ^ k) ((∑ j ∈ Finset.range r, g ^ j) w) = 0 := by
      have := congrArg (fun h : Module.End (ZMod 2) V => h w) hcommSN
      simp only [Module.End.mul_apply] at this
      rw [this, hSw, map_zero]
    have hev : (∑ i ∈ Finset.range r, (P ^ i * (∑ j ∈ Finset.range r, g ^ j) * P' ^ i)) w = w := by
      rw [hop, LinearMap.add_apply, hr1, Module.End.mul_apply, LinearMap.sub_apply,
        Module.End.one_apply, map_sub, hcn, hSw, sub_zero, add_zero]
    have hfterm : ∀ i : ℕ, f ((P ^ i) ((∑ j ∈ Finset.range r, g ^ j) ((P' ^ i) w))) =
        (P ^ i) ((∑ j ∈ Finset.range r, g ^ j) ((P' ^ i) w)) := by
      intro i
      have h1 := congrArg (fun h : Module.End (ZMod 2) V => h
        ((∑ j ∈ Finset.range r, g ^ j) ((P' ^ i) w))) (hPi_f i)
      simp only [Module.End.mul_apply] at h1
      rw [← h1, hffix _ (hNgfix _)]
    have hfw : f w = w := by
      have h2 : f ((∑ i ∈ Finset.range r, (P ^ i * (∑ j ∈ Finset.range r, g ^ j) * P' ^ i)) w) =
          (∑ i ∈ Finset.range r, (P ^ i * (∑ j ∈ Finset.range r, g ^ j) * P' ^ i)) w := by
        rw [LinearMap.sum_apply, map_sum]
        exact Finset.sum_congr rfl fun i _ => hfterm i
      rwa [hev] at h2
    have hfk : ∀ k : ℕ, (f ^ k) w = w := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ, Module.End.mul_apply, hfw, ih]
    have hSw' : (∑ k ∈ Finset.range r, f ^ k) w = w := by
      rw [LinearMap.sum_apply]
      simp only [hfk, Finset.sum_const, Finset.card_range]
      exact odd_nsmul_vec_uc6 hrodd w
    rw [← hw, ← hSw', hSw]
  exact LinearMap.ext fun x => by simpa [sub_eq_zero] using hz x

end One

end CFSG.LocalAnalysis.UniquenessCase.UC6

module

public import CFSG.RankThree.PartTwo.Sec11.Item116R2NoNum
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec11.R2No

variable {G : Type*} [Group G]

theorem pow_eq_pow_of_modEq {g : G} {N : ℕ} (hg : g ^ N = 1) {a b : ℕ} (h : a ≡ b [MOD N]) :
    g ^ a = g ^ b :=
  (pow_eq_pow_iff_modEq).mpr (h.of_dvd (orderOf_dvd_of_pow_eq_one hg))

theorem conj_pow_pow {r z : G} {u : ℕ} (h : r * z * r⁻¹ = z ^ u) (i s : ℕ) :
    r ^ i * z ^ s * (r ^ i)⁻¹ = z ^ (s * u ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : r ^ (i + 1) * z ^ s * (r ^ (i + 1))⁻¹ = r * (r ^ i * z ^ s * (r ^ i)⁻¹) * r⁻¹ := by
      rw [pow_succ', mul_inv_rev]; group
    rw [e, ih, ← conj_pow, h, ← pow_mul]
    congr 1
    ring

theorem mul_normal_form {z c r : G} {u u' : ℕ} (hzc : z * c = c * z)
    (hrz : r * z * r⁻¹ = z ^ u) (hrc : r * c * r⁻¹ = c ^ u') (s t i s' t' j : ℕ) :
    (z ^ s * c ^ t * r ^ i) * (z ^ s' * c ^ t' * r ^ j) =
      z ^ (s + s' * u ^ i) * c ^ (t + t' * u' ^ i) * r ^ (i + j) := by
  have h1 := conj_pow_pow hrz i s'
  have h2 := conj_pow_pow hrc i t'
  have hcomm : Commute (c ^ t) (z ^ (s' * u ^ i)) := (Commute.pow_pow hzc.symm t _)
  have e : (z ^ s * c ^ t * r ^ i) * (z ^ s' * c ^ t' * r ^ j) =
      z ^ s * (c ^ t * (r ^ i * z ^ s' * (r ^ i)⁻¹) * (r ^ i * c ^ t' * (r ^ i)⁻¹)) * r ^ (i + j) := by
    rw [pow_add]; group
  rw [e, h1, h2, hcomm.eq, pow_add z, pow_add c]
  group

theorem pow_normal_form {z c r : G} {u u' : ℕ} (hzc : z * c = c * z)
    (hrz : r * z * r⁻¹ = z ^ u) (hrc : r * c * r⁻¹ = c ^ u') (s t i m : ℕ) :
    (z ^ s * c ^ t * r ^ i) ^ m =
      z ^ (s * ∑ k ∈ Finset.range m, u ^ (i * k)) *
        c ^ (t * ∑ k ∈ Finset.range m, u' ^ (i * k)) * r ^ (i * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := conj_pow_pow hrz (i * m) s
    have h2 := conj_pow_pow hrc (i * m) t
    have hcomm : Commute (c ^ (t * ∑ k ∈ Finset.range m, u' ^ (i * k)))
        (z ^ (s * u ^ (i * m))) := Commute.pow_pow hzc.symm _ _
    have e : (z ^ s * c ^ t * r ^ i) ^ (m + 1) =
        z ^ (s * ∑ k ∈ Finset.range m, u ^ (i * k)) *
          (c ^ (t * ∑ k ∈ Finset.range m, u' ^ (i * k)) *
            (r ^ (i * m) * z ^ s * (r ^ (i * m))⁻¹) * (r ^ (i * m) * c ^ t * (r ^ (i * m))⁻¹)) *
          r ^ (i * (m + 1)) := by
      rw [pow_succ, ih, mul_add, pow_add, mul_one]; group
    rw [e, h1, h2, hcomm.eq, Finset.sum_range_succ, Finset.sum_range_succ, mul_add s, mul_add t,
      pow_add z, pow_add c]
    group

theorem power_map_mul {z c r : G} {u u' m : ℕ} (hzc : z * c = c * z)
    (hrz : r * z * r⁻¹ = z ^ u) (hrc : r * c * r⁻¹ = c ^ u') (hu : u % 3 = 1) (hu' : u' % 3 = 1)
    (hzw : z ^ 3 ^ (m + 1) = 1) (hcw : c ^ 3 ^ (m + 1) = 1) (s t i s' t' j : ℕ) :
    ((z ^ s * c ^ t * r ^ i) * (z ^ s' * c ^ t' * r ^ j)) ^ 3 ^ m =
      (z ^ s * c ^ t * r ^ i) ^ 3 ^ m * (z ^ s' * c ^ t' * r ^ j) ^ 3 ^ m := by
  have hmod1 : ∀ k : ℕ, (u ^ k) % 3 = 1 := fun k => by rw [Nat.pow_mod, hu]; simp
  have hmod2 : ∀ k : ℕ, (u' ^ k) % 3 = 1 := fun k => by rw [Nat.pow_mod, hu']; simp
  have hmod' : ∀ {w' : ℕ}, w' % 3 = 1 → ∀ e : ℕ, (w' ^ e) % 3 = 1 := fun {w'} hw' e => by
    rw [Nat.pow_mod, hw']; simp
  have hz1 : ∀ (a w' e : ℕ), w' % 3 = 1 →
      z ^ (a * ∑ k ∈ Finset.range (3 ^ m), w' ^ (e * k)) = z ^ (a * 3 ^ m) := fun a w' e hw' => by
    have h := geom_sum_three_pow_modEq (hmod' hw' e) m
    have hsum : ∑ k ∈ Finset.range (3 ^ m), w' ^ (e * k) =
        ∑ k ∈ Finset.range (3 ^ m), (w' ^ e) ^ k :=
      Finset.sum_congr rfl fun k _ => pow_mul w' e k
    rw [hsum]
    exact pow_eq_pow_of_modEq hzw (h.mul_left a)
  have hc1 : ∀ (a w' e : ℕ), w' % 3 = 1 →
      c ^ (a * ∑ k ∈ Finset.range (3 ^ m), w' ^ (e * k)) = c ^ (a * 3 ^ m) := fun a w' e hw' => by
    have h := geom_sum_three_pow_modEq (hmod' hw' e) m
    have hsum : ∑ k ∈ Finset.range (3 ^ m), w' ^ (e * k) =
        ∑ k ∈ Finset.range (3 ^ m), (w' ^ e) ^ k :=
      Finset.sum_congr rfl fun k _ => pow_mul w' e k
    rw [hsum]
    exact pow_eq_pow_of_modEq hcw (h.mul_left a)
  rw [mul_normal_form hzc hrz hrc s t i s' t' j,
    pow_normal_form hzc hrz hrc (s + s' * u ^ i) (t + t' * u' ^ i) (i + j) (3 ^ m),
    pow_normal_form hzc hrz hrc s t i (3 ^ m), pow_normal_form hzc hrz hrc s' t' j (3 ^ m)]
  rw [hz1 _ u _ hu, hz1 _ u _ hu, hz1 _ u _ hu, hc1 _ u' _ hu', hc1 _ u' _ hu', hc1 _ u' _ hu']
  rw [mul_normal_form hzc hrz hrc (s * 3 ^ m) (t * 3 ^ m) (i * 3 ^ m) (s' * 3 ^ m) (t' * 3 ^ m)
    (j * 3 ^ m)]
  have a1 : ∀ {v : ℕ}, v % 3 = 1 → v * 3 ^ m ≡ 3 ^ m [MOD 3 ^ (m + 1)] := fun {v} hv => by
    simpa [mul_comm] using three_pow_mul_modEq hv m
  have a2 : ∀ {v : ℕ}, v % 3 = 1 → 3 ^ m * v ^ 3 ^ m ≡ 3 ^ m [MOD 3 ^ (m + 1)] := fun {v} hv => by
    simpa using (pow_three_pow_modEq hv m).mul_left (3 ^ m)
  have hz2 : z ^ ((s + s' * u ^ i) * 3 ^ m) = z ^ (s * 3 ^ m + s' * 3 ^ m * u ^ (i * 3 ^ m)) := by
    refine pow_eq_pow_of_modEq hzw ?_
    have e1 : (s + s' * u ^ i) * 3 ^ m = s * 3 ^ m + s' * (u ^ i * 3 ^ m) := by ring
    have e2 : s * 3 ^ m + s' * 3 ^ m * u ^ (i * 3 ^ m) =
        s * 3 ^ m + s' * (3 ^ m * (u ^ i) ^ 3 ^ m) := by rw [mul_comm i, pow_mul]; ring
    rw [e1, e2]
    exact ((a1 (hmod1 i)).mul_left s').add_left _ |>.trans
      (((a2 (hmod1 i)).mul_left s').add_left _).symm
  have hc2 : c ^ ((t + t' * u' ^ i) * 3 ^ m) = c ^ (t * 3 ^ m + t' * 3 ^ m * u' ^ (i * 3 ^ m)) := by
    refine pow_eq_pow_of_modEq hcw ?_
    have e1 : (t + t' * u' ^ i) * 3 ^ m = t * 3 ^ m + t' * (u' ^ i * 3 ^ m) := by ring
    have e2 : t * 3 ^ m + t' * 3 ^ m * u' ^ (i * 3 ^ m) =
        t * 3 ^ m + t' * (3 ^ m * (u' ^ i) ^ 3 ^ m) := by rw [mul_comm i, pow_mul]; ring
    rw [e1, e2]
    exact ((a1 (hmod2 i)).mul_left t').add_left _ |>.trans
      (((a2 (hmod2 i)).mul_left t').add_left _).symm
  rw [hz2, hc2, add_mul i j]

end CFSG.RankThree.PartTwo.Sec11.R2No

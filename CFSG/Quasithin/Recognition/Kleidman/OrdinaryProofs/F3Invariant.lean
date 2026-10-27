module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Charpoly.Basic

public section

namespace CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs

open Polynomial

namespace F3Invariant

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

lemma adj_step (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (g : V ≃ₗ[ZMod 2] V)
    (hgB : ∀ v w, B (g v) (g w) = B v w) (x y : V) :
    B ((g.symm : V →ₗ[ZMod 2] V) x) y = B x ((g : V →ₗ[ZMod 2] V) y) := by
  have h := hgB (g.symm x) y
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h ⊢
  exact h.symm

lemma adj_pow (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (g : V ≃ₗ[ZMod 2] V)
    (hgB : ∀ v w, B (g v) (g w) = B v w) (n : ℕ) :
    ∀ x y : V, B (((g.symm : V →ₗ[ZMod 2] V) ^ n) x) y
      = B x (((g : V →ₗ[ZMod 2] V) ^ n) y) := by
  induction n with
  | zero => intro x y; simp
  | succ n ih =>
    intro x y
    have hL : ((g.symm : V →ₗ[ZMod 2] V) ^ (n + 1)) x
        = (g.symm : V →ₗ[ZMod 2] V) (((g.symm : V →ₗ[ZMod 2] V) ^ n) x) := by
      rw [pow_succ', Module.End.mul_apply]
    have hR : ((g : V →ₗ[ZMod 2] V) ^ (n + 1)) y
        = ((g : V →ₗ[ZMod 2] V) ^ n) ((g : V →ₗ[ZMod 2] V) y) := by
      rw [pow_succ, Module.End.mul_apply]
    rw [hL, hR, adj_step B g hgB, ih]

lemma adj_aeval (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (g : V ≃ₗ[ZMod 2] V)
    (hgB : ∀ v w, B (g v) (g w) = B v w) (p : (ZMod 2)[X]) (x y : V) :
    B (aeval (g.symm : V →ₗ[ZMod 2] V) p x) y
      = B x (aeval (g : V →ₗ[ZMod 2] V) p y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq, map_add]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul, map_smul,
      LinearMap.smul_apply, adj_pow B g hgB n]

lemma aeval_symm_eq_zero (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (g : V ≃ₗ[ZMod 2] V)
    (hgB : ∀ v w, B (g v) (g w) = B v w)
    (hnd : ∀ v : V, (∀ w, B v w = 0) → v = 0)
    (p : (ZMod 2)[X]) (hp : aeval (g : V →ₗ[ZMod 2] V) p = 0) :
    aeval (g.symm : V →ₗ[ZMod 2] V) p = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.zero_apply]
  refine hnd _ fun w => ?_
  rw [adj_aeval B g hgB p v w]
  have h := LinearMap.congr_fun hp w
  rw [LinearMap.zero_apply] at h
  rw [h, map_zero]

lemma aeval_reflect_mul_pow {A : Type*} [Ring A] [Algebra (ZMod 2) A]
    (G H : A) (hGH : G * H = 1) (hHG : H * G = 1) (N : ℕ) (f : (ZMod 2)[X])
    (hf : f.natDegree ≤ N) : aeval G (reflect N f) * H ^ N = aeval H f := by
  have hc : Commute G H := hGH.trans hHG.symm
  have hk : ∀ k : ℕ, G ^ k * H ^ k = 1 := fun k => by
    rw [← hc.mul_pow, hGH, one_pow]
  refine induction_with_natDegree_le (fun f => aeval G (reflect N f) * H ^ N = aeval H f)
    N ?_ ?_ ?_ f hf
  · simp
  · intro n r _ hnN
    have hN : H ^ N = H ^ (N - n) * H ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hnN]
    simp only [reflect_C_mul_X_pow, revAt_le hnN, map_mul, aeval_C, aeval_X_pow]
    rw [hN, mul_assoc, ← mul_assoc (G ^ (N - n)), hk, one_mul]
  · intro f1 f2 _ _ h1 h2
    rw [reflect_add, map_add, add_mul, h1, h2, map_add]

lemma aeval_reverse_of_aeval_symm {A : Type*} [Ring A] [Algebra (ZMod 2) A]
    (G H : A) (hGH : G * H = 1) (hHG : H * G = 1) (p : (ZMod 2)[X])
    (hp : aeval H p = 0) : aeval G p.reverse = 0 := by
  have h1 : aeval G (reflect p.natDegree p) * H ^ p.natDegree = aeval H p :=
    aeval_reflect_mul_pow G H hGH hHG p.natDegree p le_rfl
  rw [hp] at h1
  have hc : Commute H G := hHG.trans hGH.symm
  have hd : H ^ p.natDegree * G ^ p.natDegree = 1 := by
    rw [← hc.mul_pow, hHG, one_pow]
  change aeval G (reflect p.natDegree p) = 0
  calc aeval G (reflect p.natDegree p)
      = aeval G (reflect p.natDegree p) * (H ^ p.natDegree * G ^ p.natDegree) := by
        rw [hd, mul_one]
    _ = (aeval G (reflect p.natDegree p) * H ^ p.natDegree) * G ^ p.natDegree := by
        rw [mul_assoc]
    _ = 0 := by rw [h1, zero_mul]

lemma minpoly_reverse_eq {A : Type*} [Ring A] [Algebra (ZMod 2) A]
    (G H : A) (hGH : G * H = 1) (hHG : H * G = 1) (hint : IsIntegral (ZMod 2) G)
    (hH : aeval H (minpoly (ZMod 2) G) = 0) :
    (minpoly (ZMod 2) G).reverse = minpoly (ZMod 2) G := by
  set p := minpoly (ZMod 2) G with hp_def
  have hrev : aeval G p.reverse = 0 := aeval_reverse_of_aeval_symm G H hGH hHG p hH
  obtain ⟨q, hq⟩ := minpoly.dvd (ZMod 2) G hrev
  have hne : p.reverse ≠ 0 := by
    rw [Ne, reverse_eq_zero]
    exact minpoly.ne_zero hint
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hne
    rw [hq, mul_zero]
  have hdeg : p.reverse.natDegree ≤ p.natDegree := reverse_natDegree_le p
  rw [hq, natDegree_mul hp0 hq0] at hdeg
  have hq_deg : q.natDegree = 0 := by omega
  have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hq_deg
  have hc : q.coeff 0 = 1 := by
    have hc0 : q.coeff 0 ≠ 0 := by
      intro h
      apply hq0
      rw [hqC, h, C_0]
    have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    exact key _ hc0
  rw [hq, hqC, hc, C_1, mul_one]

lemma natDegree_minpoly_le_four {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hfin : Module.finrank (ZMod 2) V = 4)
    (G : V →ₗ[ZMod 2] V) : (minpoly (ZMod 2) G).natDegree ≤ 4 := by
  have hd : aeval G (LinearMap.charpoly G) = 0 := LinearMap.aeval_self_charpoly G
  have hdvd := minpoly.dvd (ZMod 2) G hd
  have hne : LinearMap.charpoly G ≠ 0 := (LinearMap.charpoly_monic G).ne_zero
  have h := Polynomial.natDegree_le_of_dvd hdvd hne
  rwa [LinearMap.charpoly_natDegree, hfin] at h

lemma two_eq_zero_poly : (2 : (ZMod 2)[X]) = 0 := by
  have h2 : (2 : (ZMod 2)[X]) = C (2 : ZMod 2) := (map_ofNat C 2).symm
  have h0 : (2 : ZMod 2) = 0 := rfl
  rw [h2, h0, C_0]

lemma eq_sum5 (p : (ZMod 2)[X]) (h : p.natDegree ≤ 4) :
    p = C (p.coeff 0) + C (p.coeff 1) * X + C (p.coeff 2) * X ^ 2
      + C (p.coeff 3) * X ^ 3 + C (p.coeff 4) * X ^ 4 := by
  conv_lhs => rw [as_sum_range' p 5 (by omega)]
  simp [Finset.sum_range_succ, ← C_mul_X_pow_eq_monomial]

lemma coeff_sym (p : (ZMod 2)[X]) (hrev : p.reverse = p) (i : ℕ) :
    p.coeff (revAt p.natDegree i) = p.coeff i := by
  have h := congrArg (fun q : (ZMod 2)[X] => q.coeff i) hrev
  simpa only [coeff_reverse] using h

lemma zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

lemma shape_d1 (p : (ZMod 2)[X]) (hd : p.natDegree = 1) (hm : p.Monic) (h0 : p.coeff 0 = 1) :
    p = X + 1 := by
  have hl : p.coeff 1 = 1 := by
    have := hm.coeff_natDegree
    rwa [hd] at this
  have e := eq_sum5 p (by omega)
  have h2 : p.coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h3 : p.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h4 : p.coeff 4 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [h0, hl, h2, h3, h4] at e
  rw [e]
  simp only [map_one, map_zero, one_mul, zero_mul, add_zero]
  ring

lemma shape_d2 (p : (ZMod 2)[X]) (hd : p.natDegree = 2) (hm : p.Monic) (h0 : p.coeff 0 = 1) :
    p = X ^ 2 + 1 ∨ p = X ^ 2 + X + 1 := by
  have hl : p.coeff 2 = 1 := by
    have := hm.coeff_natDegree
    rwa [hd] at this
  have e := eq_sum5 p (by omega)
  have h3 : p.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h4 : p.coeff 4 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  rw [h0, hl, h3, h4] at e
  rcases zmod2_cases (p.coeff 1) with h1 | h1
  · left
    rw [h1] at e
    rw [e]
    simp only [map_one, map_zero, one_mul, zero_mul, add_zero]
    ring
  · right
    rw [h1] at e
    rw [e]
    simp only [map_one, map_zero, one_mul, zero_mul, add_zero]
    ring

lemma shape_d3 (p : (ZMod 2)[X]) (hd : p.natDegree = 3) (hm : p.Monic) (h0 : p.coeff 0 = 1)
    (hrev : p.reverse = p) : p = X ^ 3 + 1 ∨ p = X ^ 3 + X ^ 2 + X + 1 := by
  have hl : p.coeff 3 = 1 := by
    have := hm.coeff_natDegree
    rwa [hd] at this
  have e := eq_sum5 p (by omega)
  have h4 : p.coeff 4 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hs : p.coeff 2 = p.coeff 1 := by
    have := coeff_sym p hrev 1
    rw [hd, revAt_le (by norm_num)] at this
    simpa using this
  rw [h0, hl, h4, hs] at e
  rcases zmod2_cases (p.coeff 1) with h1 | h1
  · left
    rw [h1] at e
    rw [e]
    simp only [map_one, map_zero, one_mul, zero_mul, add_zero]
    ring
  · right
    rw [h1] at e
    rw [e]
    simp only [map_one, map_zero, one_mul, zero_mul, add_zero]
    ring

lemma shape_d4 (p : (ZMod 2)[X]) (hd : p.natDegree = 4) (hm : p.Monic) (h0 : p.coeff 0 = 1)
    (hrev : p.reverse = p) :
    p = X ^ 4 + 1 ∨ p = X ^ 4 + X ^ 3 + X + 1 ∨ p = X ^ 4 + X ^ 2 + 1
      ∨ p = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  have hl : p.coeff 4 = 1 := by
    have := hm.coeff_natDegree
    rwa [hd] at this
  have e := eq_sum5 p (by omega)
  have hs1 : p.coeff 3 = p.coeff 1 := by
    have := coeff_sym p hrev 1
    rw [hd, revAt_le (by norm_num)] at this
    simpa using this
  rw [h0, hl, hs1] at e
  rcases zmod2_cases (p.coeff 1) with h1 | h1 <;> rcases zmod2_cases (p.coeff 2) with h2 | h2
  · left
    rw [h1, h2] at e
    rw [e]
    simp only [map_one, map_zero, one_mul, zero_mul, add_zero]
    ring
  · right; right; left
    rw [h1, h2] at e
    rw [e]
    simp only [map_one, map_zero, one_mul, zero_mul, add_zero]
    ring
  · right; left
    rw [h1, h2] at e
    rw [e]
    simp only [map_one, map_zero, one_mul, zero_mul, add_zero]
    ring
  · right; right; right
    rw [h1, h2] at e
    rw [e]
    simp only [map_one, map_zero, one_mul, zero_mul, add_zero]
    ring

lemma exists_dvd_X_pow_sub_one (p : (ZMod 2)[X]) (hm : p.Monic) (h0 : p.coeff 0 = 1)
    (hrev : p.reverse = p) (hd : p.natDegree ≤ 4) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 6 ∧ p ∣ X ^ k - 1 := by
  have hdeg : p.natDegree = 0 ∨ p.natDegree = 1 ∨ p.natDegree = 2 ∨ p.natDegree = 3
      ∨ p.natDegree = 4 := by omega
  rcases hdeg with h | h | h | h | h
  · refine ⟨1, le_rfl, by norm_num, ?_⟩
    have hp : p = 1 := by
      rw [eq_C_of_natDegree_eq_zero h, h0, C_1]
    rw [hp]
    exact one_dvd _
  · refine ⟨1, le_rfl, by norm_num, ?_⟩
    rw [shape_d1 p h hm h0]
    exact ⟨1, by linear_combination (-1 : (ZMod 2)[X]) * two_eq_zero_poly⟩
  · rcases shape_d2 p h hm h0 with rfl | rfl
    · refine ⟨2, by norm_num, by norm_num, ?_⟩
      exact ⟨1, by linear_combination (-1 : (ZMod 2)[X]) * two_eq_zero_poly⟩
    · refine ⟨3, by norm_num, by norm_num, ?_⟩
      exact ⟨X + 1, by linear_combination (-(X ^ 2 + X + 1 : (ZMod 2)[X])) * two_eq_zero_poly⟩
  · rcases shape_d3 p h hm h0 hrev with rfl | rfl
    · refine ⟨3, by norm_num, by norm_num, ?_⟩
      exact ⟨1, by linear_combination (-1 : (ZMod 2)[X]) * two_eq_zero_poly⟩
    · refine ⟨4, by norm_num, by norm_num, ?_⟩
      exact ⟨X + 1, by
        linear_combination (-(X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X])) * two_eq_zero_poly⟩
  · rcases shape_d4 p h hm h0 hrev with rfl | rfl | rfl | rfl
    · refine ⟨4, by norm_num, by norm_num, ?_⟩
      exact ⟨1, by linear_combination (-1 : (ZMod 2)[X]) * two_eq_zero_poly⟩
    · refine ⟨6, by norm_num, by norm_num, ?_⟩
      exact ⟨X ^ 2 + X + 1, by
        linear_combination (-(X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]))
          * two_eq_zero_poly⟩
    · refine ⟨6, by norm_num, by norm_num, ?_⟩
      exact ⟨X ^ 2 + 2 * X + 1, by
        linear_combination (-(X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X]))
          * two_eq_zero_poly⟩
    · refine ⟨5, by norm_num, by norm_num, ?_⟩
      exact ⟨X + 1, by
        linear_combination (-(X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 2)[X])) * two_eq_zero_poly⟩

lemma pow_eq_one_of_dvd {A : Type*} [Ring A] [Algebra (ZMod 2) A] (G : A)
    (p : (ZMod 2)[X]) (k : ℕ) (hp : aeval G p = 0) (hdvd : p ∣ (X ^ k - 1 : (ZMod 2)[X])) :
    G ^ k = 1 := by
  obtain ⟨q, hq⟩ := hdvd
  have h : aeval G (X ^ k - 1 : (ZMod 2)[X]) = 0 := by
    rw [hq, map_mul, hp, zero_mul]
  rw [map_sub, aeval_X_pow, map_one, sub_eq_zero] at h
  exact h

lemma linearEquiv_pow_apply (g : V ≃ₗ[ZMod 2] V) (n : ℕ) (v : V) :
    (g ^ n) v = ((g : V →ₗ[ZMod 2] V) ^ n) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply]
    exact ih (g v)

theorem orderOf_ne_fifteen [FiniteDimensional (ZMod 2) V] (hfin : Module.finrank (ZMod 2) V = 4)
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hnd : ∀ v : V, (∀ w, B v w = 0) → v = 0)
    (g : V ≃ₗ[ZMod 2] V) (hgB : ∀ v w, B (g v) (g w) = B v w) :
    orderOf g ≠ 15 := by
  intro h15
  have hGH : (g : V →ₗ[ZMod 2] V) * (g.symm : V →ₗ[ZMod 2] V) = 1 := by
    ext v; simp
  have hHG : (g.symm : V →ₗ[ZMod 2] V) * (g : V →ₗ[ZMod 2] V) = 1 := by
    ext v; simp
  have hint : IsIntegral (ZMod 2) (g : V →ₗ[ZMod 2] V) :=
    ⟨LinearMap.charpoly _, LinearMap.charpoly_monic _, LinearMap.aeval_self_charpoly _⟩
  have hp0 : aeval (g : V →ₗ[ZMod 2] V) (minpoly (ZMod 2) (g : V →ₗ[ZMod 2] V)) = 0 :=
    minpoly.aeval _ _
  have hH := aeval_symm_eq_zero B g hgB hnd _ hp0
  have hrev := minpoly_reverse_eq _ _ hGH hHG hint hH
  have hmonic := minpoly.monic hint
  have hdeg := natDegree_minpoly_le_four hfin (g : V →ₗ[ZMod 2] V)
  have h0 : (minpoly (ZMod 2) (g : V →ₗ[ZMod 2] V)).coeff 0 = 1 := by
    have h := coeff_zero_reverse (minpoly (ZMod 2) (g : V →ₗ[ZMod 2] V))
    rw [hrev, hmonic.leadingCoeff] at h
    exact h
  obtain ⟨k, hk1, hk6, hdvd⟩ := exists_dvd_X_pow_sub_one _ hmonic h0 hrev hdeg
  have hGk : (g : V →ₗ[ZMod 2] V) ^ k = 1 := pow_eq_one_of_dvd _ _ k hp0 hdvd
  have hgk : g ^ k = 1 := by
    refine LinearEquiv.ext fun v => ?_
    rw [linearEquiv_pow_apply, LinearMap.congr_fun hGk v]
    rfl
  have hdiv : orderOf g ∣ k := orderOf_dvd_of_pow_eq_one hgk
  rw [h15] at hdiv
  have := Nat.le_of_dvd (by omega) hdiv
  omega

theorem no_commuting_five_three [FiniteDimensional (ZMod 2) V]
    (hfin : Module.finrank (ZMod 2) V = 4)
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hnd : ∀ v : V, (∀ w, B v w = 0) → v = 0)
    (f r : V ≃ₗ[ZMod 2] V) (hc : Commute f r) (hf : orderOf f = 5) (hr : orderOf r = 3)
    (hfB : ∀ v w, B (f v) (f w) = B v w) (hrB : ∀ v w, B (r v) (r w) = B v w) : False := by
  have hco : Nat.Coprime (orderOf f) (orderOf r) := by
    rw [hf, hr]; norm_num
  have h15 : orderOf (f * r) = 15 := by
    rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime hco, hf, hr]
  refine orderOf_ne_fifteen hfin B hnd (f * r) (fun v w => ?_) h15
  show B (f (r v)) (f (r w)) = B v w
  exact (hfB (r v) (r w)).trans (hrB v w)

end F3Invariant

end CFSG.Quasithin.Recognition.Kleidman.OrdinaryProofs

module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5A
public import Mathlib
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra Polynomial Module

local notation "F" => OmegaField

section OddNormalizer

variable {G : Type*} [Group G]

private theorem s16h_e3_z3f5_mod_five_aux (a : ℕ) (ha : a < 5) (r : ℕ) (hr : r < 4)
    (hodd : r % 2 = 1) (h : a ^ r % 5 = 1) : a = 1 := by
  have key : ∀ a : Fin 5, ∀ r : Fin 4, (r : ℕ) % 2 = 1 → (a : ℕ) ^ (r : ℕ) % 5 = 1 →
      (a : ℕ) = 1 := by decide
  exact key ⟨a, ha⟩ ⟨r, hr⟩ hodd h

private theorem s16h_e3_z3f5_pow_mod_five_reduce (a o : ℕ) (ha : a % 5 ≠ 0) :
    a ^ o % 5 = (a % 5) ^ (o % 4) % 5 := by
  have h4 : (a % 5) ^ 4 % 5 = 1 := by
    have : ∀ b < 5, b ≠ 0 → b ^ 4 % 5 = 1 := by decide
    exact this _ (Nat.mod_lt _ (by norm_num)) ha
  conv_lhs => rw [← Nat.div_add_mod o 4, Nat.pow_mod, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod,
    h4, one_pow, Nat.one_mod, one_mul, Nat.mod_mod]

theorem s16h_e3_z3f5_commute_of_odd_of_orderOf_five {x n : G} (hx : orderOf x = 5)
    (hn : Odd (orderOf n)) (hc : n * x * n⁻¹ ∈ Subgroup.zpowers x) : n * x = x * n := by
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hc
  set k : ℕ := (z % 5).toNat with hkdef
  have hk : x ^ k = n * x * n⁻¹ := by
    rw [← hz, ← zpow_mod_orderOf, hx]
    have h0 : 0 ≤ z % 5 := Int.emod_nonneg _ (by norm_num)
    rw [hkdef, ← zpow_natCast, Int.toNat_of_nonneg h0]
    rfl
  have hiter : ∀ j : ℕ, n ^ j * x * (n ^ j)⁻¹ = x ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc n ^ (j + 1) * x * (n ^ (j + 1))⁻¹ = n * (n ^ j * x * (n ^ j)⁻¹) * n⁻¹ := by
            simp only [pow_succ', _root_.mul_inv_rev, mul_assoc]
        _ = n * x ^ (k ^ j) * n⁻¹ := by rw [ih]
        _ = (n * x * n⁻¹) ^ (k ^ j) := by rw [_root_.conj_pow]
        _ = x ^ (k ^ (j + 1)) := by rw [← hk, ← pow_mul, ← pow_succ']
  set o := orderOf n with hodef
  have hxk : x ^ (k ^ o) = x ^ 1 := by rw [← hiter o, pow_orderOf_eq_one]; simp
  have hmod : k ^ o % 5 = 1 := by
    have := (pow_eq_pow_iff_modEq).mp hxk
    rw [hx] at this
    exact this
  have hopos : 0 < o := by obtain ⟨m, hm⟩ := hn; omega
  have hk5 : k % 5 ≠ 0 := by
    intro h0
    rw [Nat.pow_mod, h0, zero_pow hopos.ne'] at hmod
    norm_num at hmod
  have hr1 : (k % 5) ^ (o % 4) % 5 = 1 := by
    rw [← s16h_e3_z3f5_pow_mod_five_reduce k o hk5]; exact hmod
  have ha := s16h_e3_z3f5_mod_five_aux (k % 5) (Nat.mod_lt _ (by norm_num)) (o % 4)
    (Nat.mod_lt _ (by norm_num)) (by obtain ⟨m, hm⟩ := hn; omega) hr1
  have h1 : n * x * n⁻¹ = x := by rw [← hk, ← pow_mod_orderOf, hx, ha, pow_one]
  calc n * x = n * x * n⁻¹ * n := by group
    _ = x * n := by rw [h1]

end OddNormalizer

theorem s16h_e3_z3f5_eq_one_of_pow_five (c : F) (h : c ^ 5 = 1) : c = 1 := by
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at h
  rcases s16h_e3_z3f5_cube_eq_zero_or_one c with h3 | h3
  · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h3) hc0
  have h2 : c ^ 2 = 1 := by
    have : c ^ 5 = c ^ 3 * c ^ 2 := by ring
    rwa [this, h3, one_mul] at h
  have : (c + 1) ^ 2 = 0 := by
    have e : (c + 1) ^ 2 = c ^ 2 + 1 + c * 2 := by ring
    rw [e, h2, omegaField_two_eq_zero, mul_zero, add_zero, s16h_e3_z3f5_omegaField_add_self]
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have h' : c = -1 := eq_neg_of_add_eq_zero_left this
  rw [h']
  have : (-1 : F) = 1 := by
    rw [neg_eq_iff_add_eq_zero, s16h_e3_z3f5_omegaField_add_self]
  exact this

theorem s16h_e3_z3f5_pow_four_eq_self (c : F) : c ^ 4 = c := by
  rcases s16h_e3_z3f5_cube_eq_zero_or_one c with h3 | h3
  · rw [pow_eq_zero_iff (by norm_num) |>.mp h3]; norm_num
  · rw [pow_succ, h3, one_mul]

variable {V : Type*} [AddCommGroup V] [Module F V]

theorem s16h_e3_z3f5_add_self_eq_zero (v : V) : v + v = 0 := by
  rw [← two_smul F v, omegaField_two_eq_zero, zero_smul]

noncomputable def s16h_e3_z3f5_e (f : Module.End F V) : Module.End F V :=
  1 + f + f ^ 2 + f ^ 3 + f ^ 4

variable {f : Module.End F V}

theorem s16h_e3_z3f5_e_apply (v : V) :
    s16h_e3_z3f5_e f v = v + f v + (f ^ 2) v + (f ^ 3) v + (f ^ 4) v := by
  simp [s16h_e3_z3f5_e]

theorem s16h_e3_z3f5_pow_apply_succ (k : ℕ) (v : V) :
    (f ^ (k + 1)) v = f ((f ^ k) v) := by
  rw [pow_succ', Module.End.mul_apply]

theorem s16h_e3_z3f5_f_f (v : V) : f (f v) = (f ^ 2) v := by
  rw [sq, Module.End.mul_apply]

theorem s16h_e3_z3f5_f_pow (k : ℕ) (v : V) : f ((f ^ k) v) = (f ^ (k + 1)) v :=
  (s16h_e3_z3f5_pow_apply_succ k v).symm

theorem s16h_e3_z3f5_pow_f (k : ℕ) (v : V) : (f ^ k) (f v) = (f ^ (k + 1)) v := by
  rw [pow_succ, Module.End.mul_apply]

theorem s16h_e3_z3f5_f_e (hf5 : f ^ 5 = 1) (v : V) : f (s16h_e3_z3f5_e f v) =
    s16h_e3_z3f5_e f v := by
  rw [s16h_e3_z3f5_e_apply, map_add, map_add, map_add, map_add, s16h_e3_z3f5_f_f,
    s16h_e3_z3f5_f_pow 2, s16h_e3_z3f5_f_pow 3, s16h_e3_z3f5_f_pow 4, hf5,
    Module.End.one_apply]
  simp only [Nat.reduceAdd]
  abel

theorem s16h_e3_z3f5_e_comm (v : V) : s16h_e3_z3f5_e f (f v) = f (s16h_e3_z3f5_e f v) := by
  rw [s16h_e3_z3f5_e_apply, s16h_e3_z3f5_e_apply]
  simp only [map_add, s16h_e3_z3f5_f_f, s16h_e3_z3f5_f_pow, s16h_e3_z3f5_pow_f]

theorem s16h_e3_z3f5_pow_e (hf5 : f ^ 5 = 1) (k : ℕ) (v : V) :
    (f ^ k) (s16h_e3_z3f5_e f v) = s16h_e3_z3f5_e f v := by
  induction k with
  | zero => simp
  | succ k ih => rw [s16h_e3_z3f5_pow_apply_succ, ih, s16h_e3_z3f5_f_e hf5]

theorem s16h_e3_z3f5_e_e (hf5 : f ^ 5 = 1) (v : V) :
    s16h_e3_z3f5_e f (s16h_e3_z3f5_e f v) = s16h_e3_z3f5_e f v := by
  rw [s16h_e3_z3f5_e_apply (s16h_e3_z3f5_e f v), s16h_e3_z3f5_f_e hf5,
    s16h_e3_z3f5_pow_e hf5, s16h_e3_z3f5_pow_e hf5, s16h_e3_z3f5_pow_e hf5,
    s16h_e3_z3f5_add_self_eq_zero, zero_add, s16h_e3_z3f5_add_self_eq_zero, zero_add]

theorem s16h_e3_z3f5_eq_zero_of_eigen (hf5 : f ^ 5 = 1) {u : V} {c : F}
    (hu : s16h_e3_z3f5_e f u = 0) (hc : f u = c • u) : u = 0 := by
  have hpow : ∀ k : ℕ, (f ^ k) u = c ^ k • u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [s16h_e3_z3f5_pow_apply_succ, ih, map_smul, hc, smul_smul, pow_succ]
  have h5 := hpow 5
  rw [hf5, Module.End.one_apply] at h5
  have : (c ^ 5 - 1) • u = 0 := by rw [sub_smul, ← h5, one_smul, sub_self]
  rcases smul_eq_zero.mp this with h | h
  · have hc1 := s16h_e3_z3f5_eq_one_of_pow_five c (sub_eq_zero.mp h)
    rw [s16h_e3_z3f5_e_apply, hpow, hpow, hpow, hc, hc1] at hu
    simp only [one_pow, one_smul, s16h_e3_z3f5_add_self_eq_zero, zero_add] at hu
    exact hu
  · exact h

variable [FiniteDimensional F V]

theorem s16h_e3_z3f5_X_pow_five_sub_one_eq :
    (X ^ 5 - 1 : F[X]) = (X - 1) * ((X ^ 2 + C omega * X + 1) *
      (X ^ 2 + C (omega ^ 2) * X + 1)) := by
  have h2 : (2 : F[X]) = 0 := by rw [← map_ofNat C 2, omegaField_two_eq_zero, C_0]
  have hw : C omega + C (omega ^ 2) = (1 : F[X]) := by
    rw [← C_add, omega_add_omega_sq', C_1]
  have hw3 : C omega * C (omega ^ 2) = (1 : F[X]) := by
    rw [← C_mul, ← pow_succ', s16h_e3_z3f5_omega_cube, C_1]
  linear_combination (-X ^ 4 + X ^ 3 - X ^ 2 + X : F[X]) * hw + (X ^ 2 - X ^ 3) * hw3 +
    (X ^ 2 - X ^ 3) * h2
where
  omega_add_omega_sq' : omega + omega ^ 2 = 1 := by
    rw [omega_sq, ← add_assoc, s16h_e3_z3f5_omegaField_add_self, zero_add]

theorem s16h_e3_z3f5_exists_fixed (hV : finrank F V = 3) (hf5 : f ^ 5 = 1) :
    ∃ w : V, w ≠ 0 ∧ f w = w := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by rw [hV]; norm_num)
  set c := f.charpoly
  have hdeg : c.natDegree = 3 := by rw [LinearMap.charpoly_natDegree, hV]
  have hroot : ∃ μ, c.IsRoot μ := by
    by_contra hno
    push Not at hno
    have hirr : Irreducible c :=
      irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hno
    have hm : minpoly F f ∣ c := LinearMap.minpoly_dvd_charpoly f
    have hint : IsIntegral F f := Algebra.IsIntegral.isIntegral f
    have hmc : minpoly F f = c := by
      have hass := hirr.dvd_iff.mp hm
      rcases hass with hu | hass
      · exact absurd hu (minpoly.not_isUnit F f)
      · exact eq_of_monic_of_associated (minpoly.monic hint) (LinearMap.charpoly_monic f) hass.symm
    have hd : c ∣ (X - 1) * ((X ^ 2 + C omega * X + 1) *
        (X ^ 2 + C (omega ^ 2) * X + 1)) := by
      rw [← s16h_e3_z3f5_X_pow_five_sub_one_eq, ← hmc]
      exact minpoly.dvd _ _ (by simp [hf5])
    have hp := hirr.prime
    have hq₁ : (X ^ 2 + C omega * X + 1 : F[X]).natDegree = 2 := by compute_degree!
    have hq₂ : (X ^ 2 + C (omega ^ 2) * X + 1 : F[X]).natDegree = 2 := by compute_degree!
    rcases hp.dvd_or_dvd hd with h | h
    · have h1 : (X - 1 : F[X]).natDegree = 1 := by compute_degree!
      have := natDegree_le_of_dvd h (by intro h0; rw [h0] at h1; simp at h1)
      omega
    · rcases hp.dvd_or_dvd h with h | h
      · have := natDegree_le_of_dvd h (by intro h0; rw [h0] at hq₁; simp at hq₁)
        omega
      · have := natDegree_le_of_dvd h (by intro h0; rw [h0] at hq₂; simp at hq₂)
        omega
  obtain ⟨μ, hμ⟩ := hroot
  have hev : f.HasEigenvalue μ := (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hμ
  obtain ⟨w, hw⟩ := hev.exists_hasEigenvector
  have hfw : f w = μ • w := hw.apply_eq_smul
  have hpow : ∀ k : ℕ, (f ^ k) w = μ ^ k • w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [s16h_e3_z3f5_pow_apply_succ, ih, map_smul, hfw, smul_smul, pow_succ]
  have h5 := hpow 5
  rw [hf5, Module.End.one_apply] at h5
  have : (μ ^ 5 - 1) • w = 0 := by rw [sub_smul, ← h5, one_smul, sub_self]
  rcases smul_eq_zero.mp this with h | h
  · refine ⟨w, hw.2, ?_⟩
    rw [hfw, s16h_e3_z3f5_eq_one_of_pow_five μ (sub_eq_zero.mp h), one_smul]
  · exact absurd h hw.2

omit [FiniteDimensional F V] in
theorem s16h_e3_z3f5_pow_gcd_fix (y : Module.End F V) (x : V) (a b : ℕ) :
    (y ^ a) x = x → (y ^ b) x = x → (y ^ Nat.gcd a b) x = x := by
  induction a, b using Nat.gcd.induction with
  | H0 n => intro _ h; rwa [Nat.gcd_zero_left]
  | H1 m n hm ih =>
    intro ha hb
    rw [Nat.gcd_rec]
    have hmul : ∀ k, (y ^ (m * k)) x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk => rw [mul_add, mul_one, pow_add, Module.End.mul_apply, ha, ihk]
    apply ih _ ha
    have : (y ^ n) x = (y ^ (n % m)) ((y ^ (m * (n / m))) x) := by
      rw [← Module.End.mul_apply, ← pow_add, Nat.mod_add_div]
    rwa [hmul, hb, eq_comm] at this

theorem s16h_e3_z3f5_C_add_C_mul_sq (s t : F) (Y : F[X]) :
    (C s + C t * Y) ^ 2 = C (s ^ 2) + C (t ^ 2) * Y ^ 2 := by
  have h2 : (2 : F[X]) = 0 := by rw [← map_ofNat C 2, omegaField_two_eq_zero, C_0]
  rw [C_pow, C_pow]
  linear_combination (C s * C t * Y) * h2

theorem s16h_e3_z3f5_C_add_C_mul_pow_four (s t : F) (Y : F[X]) :
    (C s + C t * Y) ^ 4 = C s + C t * Y ^ 4 := by
  rw [show 4 = 2 * 2 by rfl, pow_mul, s16h_e3_z3f5_C_add_C_mul_sq,
    s16h_e3_z3f5_C_add_C_mul_sq, ← pow_mul, ← pow_mul,
    ← pow_mul, show 2 * 2 = 4 by rfl, s16h_e3_z3f5_pow_four_eq_self,
    s16h_e3_z3f5_pow_four_eq_self]

theorem s16h_e3_z3f5_eq_smul_add_smul (hV : finrank F V = 3) (hf5 : f ^ 5 = 1) (hf1 : f ≠ 1)
    {a : Module.End F V} (hcomm : Commute a f) {n : ℕ} (hn : ¬ 5 ∣ n) (ha : a ^ n = 1) :
    ∃ α μ : F, α ^ 3 = 1 ∧ μ ^ 3 = 1 ∧
      a = α • (1 - s16h_e3_z3f5_e f) + μ • s16h_e3_z3f5_e f := by
  obtain ⟨w, hw0, hfw⟩ := s16h_e3_z3f5_exists_fixed hV hf5
  have hfkw : ∀ k : ℕ, (f ^ k) w = w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [s16h_e3_z3f5_pow_apply_succ, ih, hfw]
  have hew : s16h_e3_z3f5_e f w = w := by
    rw [s16h_e3_z3f5_e_apply, hfw, hfkw, hfkw, hfkw, s16h_e3_z3f5_add_self_eq_zero, zero_add,
      s16h_e3_z3f5_add_self_eq_zero, zero_add]
  obtain ⟨u, hu0, hu⟩ : ∃ u : V, u ≠ 0 ∧ s16h_e3_z3f5_e f u = 0 := by
    have : ∃ v, s16h_e3_z3f5_e f v ≠ v := by
      by_contra h
      push Not at h
      apply hf1
      ext v
      rw [Module.End.one_apply, ← h v, s16h_e3_z3f5_f_e hf5]
    obtain ⟨v, hv⟩ := this
    exact ⟨v - s16h_e3_z3f5_e f v, sub_ne_zero.mpr hv.symm,
      by rw [map_sub, s16h_e3_z3f5_e_e hf5, sub_self]⟩
  have hefu : s16h_e3_z3f5_e f (f u) = 0 := by rw [s16h_e3_z3f5_e_comm, hu, map_zero]
  have hak : ∀ (k : ℕ) (v : V), a ((f ^ k) v) = (f ^ k) (a v) := fun k v => by
    rw [← Module.End.mul_apply, (hcomm.pow_right k).eq, Module.End.mul_apply]
  have haf : ∀ v, a (f v) = f (a v) := fun v => by
    rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]
  have hae : ∀ v, a (s16h_e3_z3f5_e f v) = s16h_e3_z3f5_e f (a v) := fun v => by
    rw [s16h_e3_z3f5_e_apply, s16h_e3_z3f5_e_apply, map_add, map_add, map_add, map_add, haf,
      hak, hak, hak]
  set b : Fin 3 → V := ![u, f u, w] with hb
  have hli : LinearIndependent F b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, hb, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
    have he := congrArg (s16h_e3_z3f5_e f) hg
    simp only [map_add, map_smul, hu, hefu, hew, smul_zero, zero_add, map_zero] at he
    have hg2 : g 2 = 0 := (smul_eq_zero.mp he).resolve_right hw0
    rw [hg2, zero_smul, add_zero] at hg
    have hg1 : g 1 = 0 := by
      by_contra h1
      have hfu : f u = (-(g 0) / g 1) • u := by
        have h' : g 1 • f u = -(g 0) • u := by rw [neg_smul]; exact eq_neg_of_add_eq_zero_right hg
        rw [← inv_smul_smul₀ h1 (f u), h', smul_smul, div_eq_inv_mul]
      exact hu0 (s16h_e3_z3f5_eq_zero_of_eigen hf5 hu hfu)
    rw [hg1, zero_smul, add_zero] at hg
    have hg0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right hu0
    intro i
    fin_cases i <;> assumption
  have hspan : Submodule.span F (Set.range b) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [hV])
  have hexp : ∀ x : V, ∃ c : Fin 3 → F, c 0 • u + c 1 • f u + c 2 • w = x := by
    intro x
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp
      (hspan ▸ Submodule.mem_top : x ∈ Submodule.span F (Set.range b))
    refine ⟨c, ?_⟩
    simpa [Fin.sum_univ_three, hb] using hc
  obtain ⟨c, hc⟩ := hexp (a u)
  have hc2 : c 2 = 0 := by
    have he := congrArg (s16h_e3_z3f5_e f) hc
    simp only [map_add, map_smul, hu, hefu, hew, smul_zero, zero_add] at he
    rw [← hae, hu, map_zero] at he
    exact (smul_eq_zero.mp he).resolve_right hw0
  rw [hc2, zero_smul, add_zero] at hc
  obtain ⟨d, hd⟩ := hexp (a w)
  have haw : a w = d 2 • w := by
    have he := congrArg (s16h_e3_z3f5_e f) hd
    simp only [map_add, map_smul, hu, hefu, hew, smul_zero, zero_add] at he
    rw [← hae, hew] at he
    exact he.symm
  set α := c 0
  set β := c 1
  set μ := d 2
  set y : Module.End F V := α • 1 + β • f with hy
  have hyv : ∀ v, y v = α • v + β • f v := fun v => by simp [hy]
  have hay : Commute a y :=
    (Commute.smul_right (Commute.one_right a) α).add_right (hcomm.smul_right β)
  have hau : a u = y u := by rw [hyv, ← hc]
  have hapow : ∀ k : ℕ, (a ^ k) u = (y ^ k) u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, ← Module.End.mul_apply, ((hay.pow_right k).eq),
        Module.End.mul_apply, hau, ← Module.End.mul_apply, ← pow_succ]
  have hyaeval : y = aeval f (C α + C β * X) := by
    simp [hy, Algebra.algebraMap_eq_smul_one]
  have hy4 : y ^ 4 = α • 1 + β • f ^ 4 := by
    rw [hyaeval, ← map_pow, s16h_e3_z3f5_C_add_C_mul_pow_four]
    simp [Algebra.algebraMap_eq_smul_one]
  have hy16 : y ^ 16 = y := by
    rw [show 16 = 4 * 4 by rfl, pow_mul, hyaeval, ← map_pow, ← map_pow,
      s16h_e3_z3f5_C_add_C_mul_pow_four, s16h_e3_z3f5_C_add_C_mul_pow_four, ← pow_mul,
      show 4 * 4 = 15 + 1 by rfl, pow_add, pow_one, show 15 = 5 * 3 by rfl, pow_mul]
    simp only [map_add, map_mul, aeval_C, aeval_X, map_pow, hf5, one_pow, one_mul]
  have hyn : (y ^ n) u = u := by rw [← hapow, ha, Module.End.one_apply]
  have hy15 : (y ^ 15) u = u := by
    obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
    have h1 : (y ^ (15 + n)) u = (y ^ n) u := by
      rw [show 15 + n = k + 16 by omega, pow_add, Module.End.mul_apply, hy16,
        ← Module.End.mul_apply, ← pow_succ, ← hk]
    rwa [pow_add, Module.End.mul_apply, hyn] at h1
  have hy3 : (y ^ 3) u = u := by
    have hg := s16h_e3_z3f5_pow_gcd_fix y u 15 n hy15 hyn
    have hgd : Nat.gcd 15 n ∣ 3 := by
      have h15 : Nat.gcd 15 n ∣ 15 := Nat.gcd_dvd_left 15 n
      have hco : ¬ 5 ∣ Nat.gcd 15 n := fun h5 => hn (h5.trans (Nat.gcd_dvd_right 15 n))
      have : Nat.gcd 15 n ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨h15, by norm_num⟩
      have hdiv : Nat.divisors 15 = {1, 3, 5, 15} := by decide
      rw [hdiv] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      revert hco
      rcases this with h | h | h | h <;> rw [h] <;> decide
    obtain ⟨r, hr⟩ := hgd
    rw [hr, pow_mul]
    clear hr
    induction r with
    | zero => simp
    | succ r ih => rw [pow_succ, Module.End.mul_apply, hg, ih]
  have hβ : β = 0 := by
    by_contra hβ
    have h4 : (y ^ 4) u = y u := by
      rw [pow_succ', Module.End.mul_apply, hy3]
    rw [hy4, hyv] at h4
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at h4
    have h4' : (f ^ 4) u = f u := smul_right_injective V hβ (add_left_cancel h4)
    have hf2 : (f ^ 2) u = u := by
      have := congrArg f h4'
      rw [s16h_e3_z3f5_f_pow, hf5, Module.End.one_apply, s16h_e3_z3f5_f_f] at this
      exact this.symm
    have hfu : f u = (1 : F) • u := by
      rw [one_smul, ← h4', show 4 = 2 + 2 by rfl, pow_add, Module.End.mul_apply, hf2, hf2]
    exact hu0 (s16h_e3_z3f5_eq_zero_of_eigen hf5 hu hfu)
  have hau' : a u = α • u := by rw [hau, hyv, hβ, zero_smul, add_zero]
  have hafu : a (f u) = α • f u := by rw [haf, hau', map_smul]
  have hcube : ∀ (γ : F) (x : V), x ≠ 0 → a x = γ • x → γ ^ 3 = 1 := by
    intro γ x hx hax
    have hpow : ∀ k : ℕ, (a ^ k) x = γ ^ k • x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hax, smul_smul,
          ← pow_succ]
    have h := hpow n
    rw [ha, Module.End.one_apply] at h
    have hγ : γ ≠ 0 := by
      rintro rfl
      rw [zero_pow (by rintro rfl; simp at hn), zero_smul] at h
      exact hx h
    rcases s16h_e3_z3f5_cube_eq_zero_or_one γ with h3 | h3
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h3) hγ
    · exact h3
  refine ⟨α, μ, hcube α u hu0 hau', hcube μ w hw0 haw, ?_⟩
  refine LinearMap.ext_on_range hspan ?_
  intro i
  fin_cases i
  · show a u = (α • (1 - s16h_e3_z3f5_e f) + μ • s16h_e3_z3f5_e f) u
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hu, sub_zero, smul_zero, add_zero, hau']
  · show a (f u) = (α • (1 - s16h_e3_z3f5_e f) + μ • s16h_e3_z3f5_e f) (f u)
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hefu, sub_zero, smul_zero, add_zero, hafu]
  · show a w = (α • (1 - s16h_e3_z3f5_e f) + μ • s16h_e3_z3f5_e f) w
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      Module.End.one_apply, hew, sub_self, smul_zero, zero_add, haw]

omit [FiniteDimensional F V] in
theorem s16h_e3_z3f5_pow_mod_five (hf5 : f ^ 5 = 1) (m : ℕ) (x : V) :
    (f ^ m) x = (f ^ (m % 5)) x := by
  conv_lhs => rw [← Nat.mod_add_div m 5, pow_add, pow_mul, hf5, one_pow, mul_one]

omit [FiniteDimensional F V] in
theorem s16h_e3_z3f5_tau_e (hf5 : f ^ 5 = 1) (τ : V →+ V) {k : ℕ} (hk : ¬ 5 ∣ k)
    (hτ : ∀ v, τ (f v) = (f ^ k) (τ v)) (v : V) :
    τ (s16h_e3_z3f5_e f v) = s16h_e3_z3f5_e f (τ v) := by
  have hτi : ∀ (i : ℕ) (v : V), τ ((f ^ i) v) = (f ^ (k * i)) (τ v) := by
    intro i
    induction i with
    | zero => intro v; simp
    | succ i ih =>
      intro v
      rw [s16h_e3_z3f5_pow_apply_succ, hτ, ih, ← Module.End.mul_apply, ← pow_add, mul_add,
        mul_one, add_comm]
  have hτ1 : τ (f v) = (f ^ (k * 1)) (τ v) := by rw [mul_one]; exact hτ v
  rw [s16h_e3_z3f5_e_apply, map_add, map_add, map_add, map_add, hτ1, hτi, hτi, hτi,
    s16h_e3_z3f5_e_apply]
  simp only [s16h_e3_z3f5_pow_mod_five hf5 (k * _), Nat.mul_mod k]
  have hr : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases hr with h | h | h | h <;> rw [h] <;> norm_num <;> abel

omit [FiniteDimensional F V] in
theorem s16h_e3_z3f5_tau_conj (τ : V →+ V)
    (hτs : ∀ (c : F) (v : V), τ (c • v) = c ^ 2 • τ v)
    (hτe : ∀ v, τ (s16h_e3_z3f5_e f v) = s16h_e3_z3f5_e f (τ v)) (α μ : F) (v : V) :
    τ ((α • (1 - s16h_e3_z3f5_e f) + μ • s16h_e3_z3f5_e f) v) =
      (α ^ 2 • (1 - s16h_e3_z3f5_e f) + μ ^ 2 • s16h_e3_z3f5_e f) (τ v) := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply]
  rw [map_add, hτs, hτs, map_sub, hτe]

omit [FiniteDimensional F V] in
theorem s16h_e3_z3f5_sq_mul_eq_one (hf5 : f ^ 5 = 1) {α μ : F} (hα : α ^ 3 = 1)
    (hμ : μ ^ 3 = 1) :
    (α ^ 2 • (1 - s16h_e3_z3f5_e f) + μ ^ 2 • s16h_e3_z3f5_e f) *
      (α • (1 - s16h_e3_z3f5_e f) + μ • s16h_e3_z3f5_e f) = 1 := by
  ext v
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.one_apply, map_add, map_sub, map_smul,
    s16h_e3_z3f5_e_e hf5, sub_self, smul_zero, add_zero, zero_add, sub_zero, smul_smul]
  rw [add_sub_cancel_right, smul_smul, ← pow_succ', ← pow_succ', hα, hμ, one_smul, one_smul,
    sub_add_cancel]

theorem s16h_e3_z3f5_three_element_of_normalizes (hV : finrank F V = 3)
    {f a : (Module.End F V)ˣ} (hf : orderOf f = 5) {m : ℕ} (ha : a ^ (3 ^ m) = 1)
    (hnorm : a * f * a⁻¹ ∈ Subgroup.zpowers f) :
    ∃ α μ : F, α ^ 3 = 1 ∧ μ ^ 3 = 1 ∧
      (a : Module.End F V) = α • (1 - s16h_e3_z3f5_e (f : Module.End F V)) +
        μ • s16h_e3_z3f5_e (f : Module.End F V) := by
  have hodd : Odd (orderOf a) :=
    (Odd.pow (by decide : Odd 3)).of_dvd_nat (orderOf_dvd_of_pow_eq_one ha)
  have hc := s16h_e3_z3f5_commute_of_odd_of_orderOf_five hf hodd hnorm
  have hcomm : Commute (a : Module.End F V) f := by
    have := congrArg Units.val hc
    simp only [Units.val_mul] at this
    exact this
  have hf5 : (f : Module.End F V) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hf, pow_orderOf_eq_one, Units.val_one]
  have hf1 : (f : Module.End F V) ≠ 1 := by
    intro h
    have : f = 1 := Units.ext h
    rw [this, orderOf_one] at hf
    norm_num at hf
  have ha' : (a : Module.End F V) ^ (3 ^ m) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
  have hn : ¬ 5 ∣ 3 ^ m := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h
    norm_num at this
  exact s16h_e3_z3f5_eq_smul_add_smul hV hf5 hf1 hcomm hn ha'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

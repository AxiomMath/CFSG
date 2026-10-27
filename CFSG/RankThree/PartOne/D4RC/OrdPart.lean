module

public import CFSG.RankThree.PartOne.D4RC.OrdKill

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem rcs_part_not_dvd {p M m' m c : ℕ} (hp : p.Prime) (hM : M = m' * c) (hm' : m' ≠ 0)
    (hc : 0 < c) (hpc : p ∣ c) (hm : m ∣ m') : ¬ p ^ padicValNat p M ∣ m := by
  have := Fact.mk hp
  intro h
  have hm0 : m ≠ 0 := fun h0 => hm' (Nat.eq_zero_of_zero_dvd (h0 ▸ hm))
  have h1 : padicValNat p M ≤ padicValNat p m := (padicValNat_dvd_iff_le hm0).mp h
  have h2 : padicValNat p m ≤ padicValNat p m' :=
    (padicValNat_dvd_iff_le hm').mp (pow_padicValNat_dvd.trans hm)
  have h3 : padicValNat p M = padicValNat p m' + padicValNat p c := by
    rw [hM, padicValNat.mul hm' hc.ne']
  have h4 : 1 ≤ padicValNat p c := one_le_padicValNat_of_dvd hc.ne' hpc
  omega

theorem rcs_phi_dvd_triality {c q : ℕ} (hc : c = 3 ∨ c = 6) (hq : 1 ≤ q) :
    phiOrd c q ∣ q ^ 8 + q ^ 4 + 1 := by
  have h1 : q ≤ q ^ 2 := by nlinarith
  have h2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  rcases hc with rfl | rfl
  · refine ⟨(q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1), ?_⟩
    simp only [phiOrd, ite_true]
    zify [h1, h2]
    ring
  · refine ⟨(q ^ 2 + q + 1) * (q ^ 4 - q ^ 2 + 1), ?_⟩
    simp only [phiOrd, show (6 : ℕ) ≠ 3 by norm_num, ite_false]
    zify [h1, h2]
    ring

theorem rcs_prime_dvd_triality {c q p : ℕ} (hc : c = 3 ∨ c = 6) (hq : 1 ≤ q)
    (hp : p ∣ phiOrd c q) : p ∣ q ^ 8 + q ^ 4 + 1 :=
  hp.trans (rcs_phi_dvd_triality hc hq)

theorem rcs_g2_part {p q : ℕ} (hp : p.Prime) (hpK : p ∣ q ^ 8 + q ^ 4 + 1) (hq : 1 < q) :
    ¬ p ^ padicValNat p (ordTrialityD4 q) ∣ ordG2 q := by
  have h1 : 0 < q ^ 6 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq)
  have h2 : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq)
  refine rcs_part_not_dvd hp (m' := ordG2 q) (c := q ^ 6 * (q ^ 8 + q ^ 4 + 1)) ?_ ?_ ?_
    (dvd_mul_of_dvd_right hpK _) dvd_rfl
  · unfold ordTrialityD4 ordG2; ring
  · unfold ordG2; positivity
  · positivity


theorem rcs_pow_sub_one_factor {x : ℕ} (hx : 1 ≤ x) (j k : ℕ) (h : j = 2 * k) :
    x ^ j - 1 = (x ^ k - 1) * (x ^ k + 1) := by
  subst h
  have h1 : 1 ≤ x ^ k := Nat.one_le_pow _ _ hx
  have h2 : 1 ≤ x ^ (2 * k) := Nat.one_le_pow _ _ hx
  zify [h1, h2]
  ring

theorem rcs_ordA_two_dvd (q : ℕ) : ordA 2 q ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have hprod : ∏ i ∈ Finset.Icc 2 (2 + 1), (q ^ i - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) := by
    rw [show Finset.Icc 2 (2 + 1) = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have hnum : ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
    unfold ordA; rw [hprod]
  rw [hnum]
  refine Nat.div_dvd_of_dvd ?_
  exact (Nat.gcd_dvd_right 3 (q - 1)).trans ((Nat.sub_one_dvd_pow_sub_one q 2).trans
    ((dvd_mul_right _ _).trans (dvd_mul_left _ _)))

theorem rcs_psl3_part {p q : ℕ} (hp : p.Prime) (hpK : p ∣ q ^ 8 + q ^ 4 + 1) (hq : 1 < q) :
    ¬ p ^ padicValNat p (ordTrialityD4 q) ∣ ordA 2 q := by
  have h1 : 0 < q ^ 3 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq)
  have h2 : 0 < q ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq)
  refine rcs_part_not_dvd hp (m' := q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))
    (c := q ^ 9 * (q ^ 3 + 1) * (q ^ 8 + q ^ 4 + 1)) ?_ ?_ ?_
    (dvd_mul_of_dvd_right hpK _) (rcs_ordA_two_dvd q)
  · unfold ordTrialityD4
    rw [rcs_pow_sub_one_factor (x := q) (by omega) 6 3 rfl]
    ring
  · positivity
  · positivity

theorem rcs_mod_aux {x a b c d : ℕ} (hx : 8 ≤ x) :
    ¬ x - 1 ∣ x ^ a * (x ^ b + x ^ c + 1) * (x ^ d + 1) := by
  intro h
  have h1 : 1 ≡ x [MOD x - 1] := (Nat.modEq_iff_dvd' (by omega)).mpr dvd_rfl
  have h2 : x ^ a * (x ^ b + x ^ c + 1) * (x ^ d + 1) ≡
      1 ^ a * (1 ^ b + 1 ^ c + 1) * (1 ^ d + 1) [MOD x - 1] :=
    ((h1.symm.pow a).mul (((h1.symm.pow b).add (h1.symm.pow c)).add Nat.ModEq.rfl)).mul
      ((h1.symm.pow d).add Nat.ModEq.rfl)
  have h3 : x ^ a * (x ^ b + x ^ c + 1) * (x ^ d + 1) ≡ 0 [MOD x - 1] :=
    (Nat.modEq_zero_iff_dvd).mpr h
  have h4 : 1 ^ a * (1 ^ b + 1 ^ c + 1) * (1 ^ d + 1) ≡ 0 [MOD x - 1] := h2.symm.trans h3
  simp only [one_pow] at h4
  have h5 : x - 1 ∣ 1 * (1 + 1 + 1) * (1 + 1) := (Nat.modEq_zero_iff_dvd).mp h4
  have h6 := Nat.le_of_dvd (by norm_num) h5
  omega

theorem rcs_sp6_aux {x : ℕ} (hx : 8 ≤ x) :
    ¬ (x - 1) * ((x ^ 2 - 1) * (x ^ 3 - 1)) ∣ ordTrialityD4 x := by
  intro h
  have h1 : 0 < x ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have h2 : 0 < x ^ 3 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have hM : ordTrialityD4 x = (x ^ 12 * (x ^ 8 + x ^ 4 + 1) * (x ^ 3 + 1)) *
      ((x ^ 2 - 1) * (x ^ 3 - 1)) := by
    unfold ordTrialityD4
    rw [rcs_pow_sub_one_factor (x := x) (by omega) 6 3 rfl]
    ring
  rw [hM] at h
  exact rcs_mod_aux hx ((Nat.mul_dvd_mul_iff_right (Nat.mul_pos h1 h2)).mp h)

theorem rcs_f4_aux {x : ℕ} (hx : 8 ≤ x) :
    ¬ (x ^ 6 - 1) * ((x ^ 4 - 1) * ((x ^ 3 - 1) * (x - 1))) ∣ ordTrialityD4 (x ^ 2) := by
  intro h
  have h1 : 0 < x ^ 6 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have h2 : 0 < x ^ 4 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) (by omega))
  have hM : ordTrialityD4 (x ^ 2) = ((x ^ 6 - 1) * (x ^ 4 - 1)) *
      (x ^ 24 * (x ^ 16 + x ^ 8 + 1) * (x ^ 6 + 1)) := by
    unfold ordTrialityD4
    have e1 : (x ^ 2) ^ 6 - 1 = (x ^ 6 - 1) * (x ^ 6 + 1) := by
      rw [← pow_mul]; exact rcs_pow_sub_one_factor (x := x) (by omega) 12 6 rfl
    have e2 : (x ^ 2) ^ 2 - 1 = x ^ 4 - 1 := by rw [← pow_mul]
    rw [e1, e2]
    ring
  rw [hM, show (x ^ 6 - 1) * ((x ^ 4 - 1) * ((x ^ 3 - 1) * (x - 1))) =
    ((x ^ 6 - 1) * (x ^ 4 - 1)) * ((x ^ 3 - 1) * (x - 1)) by ring] at h
  have h3 := (Nat.mul_dvd_mul_iff_left (Nat.mul_pos h1 h2)).mp h
  exact rcs_mod_aux hx ((dvd_mul_left (x - 1) (x ^ 3 - 1)).trans h3)

theorem rcs_ordBC_three {g : ℕ} (hg : 1 ≤ g) :
    ordBC 3 (2 ^ g) =
      (2 ^ g) ^ 9 * (((2 ^ g) ^ 2 - 1) * (((2 ^ g) ^ 4 - 1) * ((2 ^ g) ^ 6 - 1))) := by
  have e : ∏ i ∈ Finset.Icc 1 3, ((2 ^ g) ^ (2 * i) - 1) =
      ((2 ^ g) ^ 2 - 1) * (((2 ^ g) ^ 4 - 1) * ((2 ^ g) ^ 6 - 1)) := by
    rw [show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.prod_insert (by decide),
      Finset.prod_pair (by norm_num)]
  unfold ordBC
  rw [e, Nat.coprime_two_left.mpr (odd_two_pow_sub_one hg), Nat.div_one]

theorem rcs_ordF4_eq (q : ℕ) :
    ordF4 q = q ^ 24 * ((q ^ 12 - 1) * ((q ^ 8 - 1) * ((q ^ 6 - 1) * (q ^ 2 - 1)))) := by
  unfold ordF4; ring

theorem rcs_sp6_not_dvd {g : ℕ} (hg : 2 ≤ g) :
    ¬ ordBC 3 (2 ^ g) ∣ ordTrialityD4 (2 ^ (2 * g)) := by
  intro h
  have hx16 : 16 ≤ (2 ^ g) ^ 2 := by
    have h4 : 2 ^ 2 ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    calc 16 = (2 ^ 2) ^ 2 := by norm_num
      _ ≤ (2 ^ g) ^ 2 := Nat.pow_le_pow_left h4 2
  have hK : 2 ^ (2 * g) = (2 ^ g) ^ 2 := by rw [← pow_mul, mul_comm]
  have h4 : (2 ^ g) ^ 4 = ((2 ^ g) ^ 2) ^ 2 := by ring
  have h6 : (2 ^ g) ^ 6 = ((2 ^ g) ^ 2) ^ 3 := by ring
  rw [hK, rcs_ordBC_three (by omega), h4, h6] at h
  exact rcs_sp6_aux (x := (2 ^ g) ^ 2) (by omega) ((Dvd.intro_left ((2 ^ g) ^ 9) rfl).trans h)

theorem rcs_f4_not_dvd {g : ℕ} (hg : 2 ≤ g) :
    ¬ ordF4 (2 ^ g) ∣ ordTrialityD4 (2 ^ (4 * g)) := by
  intro h
  have hx16 : 16 ≤ (2 ^ g) ^ 2 := by
    have h4 : 2 ^ 2 ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
    calc 16 = (2 ^ 2) ^ 2 := by norm_num
      _ ≤ (2 ^ g) ^ 2 := Nat.pow_le_pow_left h4 2
  have hK : 2 ^ (4 * g) = ((2 ^ g) ^ 2) ^ 2 := by ring
  have h12 : (2 ^ g) ^ 12 = ((2 ^ g) ^ 2) ^ 6 := by ring
  have h8 : (2 ^ g) ^ 8 = ((2 ^ g) ^ 2) ^ 4 := by ring
  have h6 : (2 ^ g) ^ 6 = ((2 ^ g) ^ 2) ^ 3 := by ring
  rw [hK, rcs_ordF4_eq, h12, h8, h6] at h
  exact rcs_f4_aux (x := (2 ^ g) ^ 2) (by omega) ((Dvd.intro_left ((2 ^ g) ^ 24) rfl).trans h)

end CFSG.RankThree.PartOne.D4RC

module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Sections
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

open NearSolvable

theorem isSolvable_of_lt_top_psl2Even {p : ℕ} (hp : p.Prime)
    (hY : signalizerNearPSolvable p
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 p)))
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 p)))
    (hH : H ≠ ⊤) : Group.IsSolvable H := by
  by_contra hns
  have hcard := card_psl2_even hp.ne_zero
  have hcop := hY.1
  rw [hcard] at hcop
  have hp2 : p ≠ 2 := by
    rintro rfl
    revert hcop
    norm_num
  have hp3 : p ≠ 3 := by
    rintro rfl
    revert hcop
    norm_num
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h9 := two_pow_mod_nine (prime_mod_six hp hp2 hp3)
  obtain ⟨S, _, hSmodel, hSdvd⟩ := exists_model_card_dvd_of_not_isSolvable hY H hns
  have hdvd := hSdvd.trans (Subgroup.card_subgroup_dvd_card H)
  rw [hcard] at hdvd
  have hp1 : 1 ≤ p := hp.one_le
  rcases nearSimpleModel_card hp hp2 hSmodel with h | h | h | h
  · exact hH (eq_top_of_card_dvd (by rw [hcard, ← h]; exact hSdvd))
  · rw [h] at hdvd
    exact not_nine_dvd_psl2 h9
      ((nine_dvd_three_pow hp.two_le).trans ((three_pow_dvd_psl2_three p).trans hdvd))
  · rw [h] at hdvd
    exact not_two_pow_succ_dvd_psl2 hp1
      ((two_pow_succ_dvd_sq hp1).trans ((sq_dvd_suzuki _).trans hdvd))
  · rw [h] at hdvd
    exact not_two_pow_succ_dvd_psl2 hp1
      (((two_pow_succ_dvd_sq hp1).trans (pow_dvd_pow _ (by norm_num : 2 ≤ 3))).trans
        ((two_pow_cube_dvd_psu3 hodd).trans hdvd))

theorem isSolvable_of_lt_top_psl2Three {p : ℕ} (hp : p.Prime)
    (hY : signalizerNearPSolvable p
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)))
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)))
    (hH : H ≠ ⊤) : Group.IsSolvable H := by
  by_contra hns
  have hcard := card_psl2_three hp.ne_zero
  have hcop := hY.1
  rw [hcard] at hcop
  have hp2 : p ≠ 2 := by
    rintro rfl
    revert hcop
    norm_num
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3le : 3 ≤ p := by have := hp.two_le; omega
  have h8 := not_eight_dvd_psl2_three hodd
  obtain ⟨S, _, hSmodel, hSdvd⟩ := exists_model_card_dvd_of_not_isSolvable hY H hns
  have hdvd := hSdvd.trans (Subgroup.card_subgroup_dvd_card H)
  rw [hcard] at hdvd
  rcases nearSimpleModel_card hp hp2 hSmodel with h | h | h | h
  · rw [h] at hdvd
    exact h8 ((eight_dvd_two_pow hp3le).trans ((dvd_mul_right _ _).trans hdvd))
  · exact hH (eq_top_of_card_dvd (by rw [hcard, ← h]; exact hSdvd))
  · rw [h] at hdvd
    exact h8 ((eight_dvd_two_pow hp3le).trans
      (((dvd_pow_self _ two_ne_zero).trans (sq_dvd_suzuki _)).trans hdvd))
  · rw [h] at hdvd
    exact h8 ((eight_dvd_two_pow hp3le).trans
      (((dvd_pow_self _ (by norm_num : 3 ≠ 0)).trans (two_pow_cube_dvd_psu3 hodd)).trans hdvd))

theorem isSolvable_of_lt_top_sz {n : ℕ} (hp : (2 * n + 1).Prime)
    (hY : signalizerNearPSolvable (2 * n + 1) (Sz n)) (H : Subgroup (Sz n)) (hH : H ≠ ⊤) :
    Group.IsSolvable H := by
  by_contra hns
  have hcard := card_sz n
  have hp2 : 2 * n + 1 ≠ 2 := by omega
  have hodd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have hp1 : 1 ≤ 2 * n + 1 := by omega
  have h3 := two_pow_mod_three hodd
  obtain ⟨S, _, hSmodel, hSdvd⟩ := exists_model_card_dvd_of_not_isSolvable hY H hns
  have hdvd := hSdvd.trans (Subgroup.card_subgroup_dvd_card H)
  rw [hcard] at hdvd
  rcases nearSimpleModel_card hp hp2 hSmodel with h | h | h | h
  · rw [h] at hdvd
    exact not_three_dvd_suzuki h3
      ((((three_dvd_sq_sub_one h3).mul_left _).trans hdvd))
  · rw [h] at hdvd
    exact not_three_dvd_suzuki h3
      (((dvd_pow_self 3 hp.ne_zero).trans ((three_pow_dvd_psl2_three _).trans hdvd)))
  · exact hH (eq_top_of_card_dvd (by rw [hcard, ← h]; exact hSdvd))
  · rw [h] at hdvd
    exact not_two_pow_two_mul_succ_dvd_suzuki hp1
      ((two_pow_two_mul_succ_dvd_cube hp1).trans ((two_pow_cube_dvd_psu3 hodd).trans hdvd))

theorem exists_dvd_psl2Even_of_not_isSolvable_unitary
    {p : ℕ} (hp : p.Prime)
    (hY : signalizerNearPSolvable p (PSU3 2 p)) (H : Subgroup (PSU3 2 p)) (hH : H ≠ ⊤)
    (hns : ¬ Group.IsSolvable H) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 p)) ∣ Nat.card H := by
  have hcop := hY.1
  rw [card_psu3 hp.one_le] at hcop
  have hp2 : p ≠ 2 := by
    rintro rfl
    revert hcop
    norm_num
  have hp3 : p ≠ 3 := by
    rintro rfl
    revert hcop
    norm_num
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hcard := card_psu3_of_odd hodd
  have h3 := two_pow_mod_three hodd
  have h5 := two_pow_mod_five hodd
  have h9 := two_pow_mod_nine (prime_mod_six hp hp2 hp3)
  have hp3le : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨S, _, hSmodel, hSdvd⟩ := exists_model_card_dvd_of_not_isSolvable hY H hns
  have hdvd := hSdvd.trans (Subgroup.card_subgroup_dvd_card H)
  rw [hcard] at hdvd
  rcases nearSimpleModel_card hp hp2 hSmodel with h | h | h | h
  · rw [card_psl2_even hp.ne_zero, ← h]
    exact hSdvd
  · rw [h] at hdvd
    exact (not_twentyseven_dvd_psu3 h9
      ((twentyseven_dvd_three_pow hp3le).trans ((three_pow_dvd_psl2_three p).trans hdvd))).elim
  · rw [h] at hdvd
    exact (not_five_dvd_unitary h5
      ((((five_dvd_sq_add_one h5).mul_left _).mul_right _).trans
        (hdvd.trans (psu3_order_dvd h3)))).elim
  · exact absurd (eq_top_of_card_dvd (by rw [hcard, ← h]; exact hSdvd)) hH

end CFSG.SignalizerFunctorTheorem.McBride

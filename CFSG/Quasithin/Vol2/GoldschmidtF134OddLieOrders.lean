module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieBridge
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporSmall
public import CFSG.Quasithin.Background.F420Orders

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Assembly.LowTwoRank

theorem two_mul_card_alternatingGroup_fin (n : ℕ) (hn : 2 ≤ n) :
    2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [Nat.card_eq_fintype_card, two_mul_card_alternatingGroup, Fintype.card_perm, Fintype.card_fin]

theorem lieAlt : LieAlt := by
  intro n hn5 hn8
  refine noOddConfigQ_of_noPowerOvergroup (noPowerOvergroup_of_not_sq_dvd ?_)
  rintro X _ _ ⟨e⟩ p hp h5
  rw [Nat.card_congr e.toEquiv]
  have h2 := two_mul_card_alternatingGroup_fin n (by omega)
  interval_cases n
  · have : Nat.card (alternatingGroup (Fin 5)) = 2 ^ 2 * 3 ^ 1 * 5 := by
      rw [← Nat.mul_left_cancel_iff (show 0 < 2 by norm_num), h2]; simp [Nat.factorial]
    rw [this]
    exact not_sq_dvd_of_squarefree hp h5 (by decide +kernel) rfl
  · have : Nat.card (alternatingGroup (Fin 6)) = 2 ^ 3 * 3 ^ 2 * 5 := by
      rw [← Nat.mul_left_cancel_iff (show 0 < 2 by norm_num), h2]; simp [Nat.factorial]
    rw [this]
    exact not_sq_dvd_of_squarefree hp h5 (by decide +kernel) rfl
  · have : Nat.card (alternatingGroup (Fin 7)) = 2 ^ 3 * 3 ^ 2 * 35 := by
      rw [← Nat.mul_left_cancel_iff (show 0 < 2 by norm_num), h2]; simp [Nat.factorial]
    rw [this]
    exact not_sq_dvd_of_squarefree hp h5 (by decide +kernel) rfl
  · have : Nat.card (alternatingGroup (Fin 8)) = 2 ^ 6 * 3 ^ 2 * 35 := by
      rw [← Nat.mul_left_cancel_iff (show 0 < 2 by norm_num), h2]; simp [Nat.factorial]
    rw [this]
    exact not_sq_dvd_of_squarefree hp h5 (by decide +kernel) rfl

theorem liePsl45 : LiePsl45 := by
  intro n hn
  refine noOddConfigQ_of_noPowerOvergroup (noPowerOvergroup_of_not_sq_dvd ?_)
  rintro X _ _ h p hp h5
  rcases hn with rfl | rfl
  · rw [CFSG.Quasithin.F420.card_of_l42 h]
    exact not_sq_dvd_of_squarefree (α := 6) (β := 2) (u := 35) hp h5 (by decide +kernel)
      (by norm_num)
  · rw [CFSG.Quasithin.F420.card_of_l52 h]
    exact not_sq_dvd_of_squarefree (α := 10) (β := 2) (u := 1085) hp h5 (by decide +kernel)
      (by norm_num)

end CFSG.Quasithin.H13.NQCore

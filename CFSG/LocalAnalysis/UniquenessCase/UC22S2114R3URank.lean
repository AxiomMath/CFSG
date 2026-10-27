module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.S15 (rkLin)
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114r3u_card_center_dvd (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {m f : ℕ} (hm : m = 6 ∨ m = 7) (hX : LieModel (BarInf L) .PSU m 2 f) :
    Nat.card (center (Bar2 L)) ∣ 4 * Nat.gcd m (2 ^ f + 1) := by
  have hg : genericOrders .PSU m 2 f = (Nat.gcd m (2 ^ f + 1), 1) := rfl
  have hpos : 0 < Nat.gcd m (2 ^ f + 1) := Nat.gcd_pos_of_pos_right _ (Nat.succ_pos _)
  have hex : exceptionalOrders .PSU m 2 f = (1, 1) ∨ exceptionalOrders .PSU m 2 f = (2, 2) := by
    rcases hm with rfl | rfl
    · by_cases hf : f = 1
      · exact Or.inr (by rw [hf]; rfl)
      · left
        unfold exceptionalOrders
        split <;> simp_all
    · left
      unfold exceptionalOrders
      split <;> simp_all
  have hrow := griessRow_of_lieModel_classical hGA hX (by decide)
  rcases hex with hex | hex
  · have h := card_center_bar2_dvd_of_row hL (t := .PSU) (n := m) (p := 2) (f := f)
      (by rw [hg, hex]; exact Nat.mul_pos (Nat.mul_pos hpos one_pos) one_pos) hrow
    rw [hg, hex] at h
    have h' : Nat.card (center (Bar2 L)) ∣ Nat.gcd m (2 ^ f + 1) := by simpa using h
    exact h'.trans (dvd_mul_left _ _)
  · have h := card_center_bar2_dvd_of_row hL (t := .PSU) (n := m) (p := 2) (f := f)
      (by rw [hg, hex]; exact Nat.mul_pos (Nat.mul_pos hpos one_pos) (by norm_num)) hrow
    rw [hg, hex] at h
    refine h.trans (dvd_of_eq ?_)
    show Nat.gcd m (2 ^ f + 1) * 1 * (2 * 2) = 4 * Nat.gcd m (2 ^ f + 1)
    ring

theorem uc22s2114r3u_not_dvd_card_center (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {m f : ℕ} (hm : m = 6 ∨ m = 7) (hX : LieModel (BarInf L) .PSU m 2 f)
    {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) : ¬ r ∣ Nat.card (center (Bar2 L)) := by
  intro hd
  rcases (Nat.Prime.dvd_mul hr).1 (hd.trans (uc22s2114r3u_card_center_dvd hGA hL hm hX)) with
    h4 | hg
  · have := Nat.le_of_dvd (by norm_num) h4
    omega
  · have hrm := Nat.le_of_dvd (by omega) (hg.trans (Nat.gcd_dvd_left _ _))
    have hrq : r ∣ 2 ^ f + 1 := hg.trans (Nat.gcd_dvd_right _ _)
    have h7 : r = 7 := by omega
    subst h7
    have h2 : ∀ k : ℕ, 2 ^ k % 7 = 1 ∨ 2 ^ k % 7 = 2 ∨ 2 ^ k % 7 = 4 := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ]; omega
    have := h2 f
    omega

section Rank


theorem uc22s2114r3u_pRank_eq_rkLin (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {m f : ℕ} (hX : LieModel (BarInf L) .PSU m 2 f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    CFSG.Open.pRank p L = rkLin m false (2 ^ f) p (Nat.card (center (Bar2 L))) := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  rw [← pRank_bar2_eq_of_odd hp hp2]
  exact uc22p20w_pRank_psu (uc22p20x_lieOddRankChev hGA) hL.2.2
    (LieModel.statedClassicalModel (LieModel.of_mulEquiv e hX) (by decide)) hp hp2

theorem uc22s2114r3u_four_le_pRank (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {m f : ℕ} (hm : 5 ≤ m) (hX : LieModel (BarInf L) .PSU m 2 f) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : m = 5 → p ≠ 5) (hpf : p ∣ 2 ^ f + 1) :
    4 ≤ CFSG.Open.pRank p L := by
  rw [uc22s2114r3u_pRank_eq_rkLin hGA hL hX hp hp2]
  exact uc22p20v_four_le_rkLin_false_one hp (uc22p20v_eM_of_dvd hpf) hm h5

theorem uc22s2114r3u_three_le_pRank_three (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {m f : ℕ} (hm : m = 6 ∨ m = 7) (hX : LieModel (BarInf L) .PSU m 2 f) :
    3 ≤ CFSG.Open.pRank 3 L := by
  rw [uc22s2114r3u_pRank_eq_rkLin hGA hL hX Nat.prime_three (by norm_num)]
  rcases uc22p20v_eM_three_cases f with h | h
  · have := uc22p20v_rkLin_false_one (m := m) (z := Nat.card (center (Bar2 L))) h
    omega
  · rw [uc22p20v_rkLin_false_two h]
    omega

end Rank

end CFSG.LocalAnalysis.UniquenessCase.UC22

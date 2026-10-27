module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeI1
public import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s15k_schur2_card {Y : Type} [Group Y] (hY : IsAlt Y 5 ∨ IsL3 Y 1) :
    Nat.card Y = 60 ∨ Nat.card Y = 168 := by
  rcases hY with hA | hL
  · left
    obtain ⟨e⟩ := hA
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · right
    exact CFSG.Blueprint.LieModel.card_psl_three_two hL

theorem s15k_schur2_not_sq_dvd {Y : Type} [Group Y] (hY : IsAlt Y 5 ∨ IsL3 Y 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ Nat.card Y := by
  intro h
  have hN := s15k_schur2_card hY
  have hN0 : 0 < Nat.card Y := by omega
  have hle : p ^ 2 ≤ Nat.card Y := Nat.le_of_dvd hN0 h
  have hp13 : p < 13 := by
    by_contra h13
    have : 13 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hp2' := hp.two_le
  rcases hN with hN | hN <;> rw [hN] at h <;> interval_cases p <;> simp_all +decide

theorem rSchur2_153_holds : RSchur2_153 := by
  intro X _ _ hq hodd hY
  haveI : Group.IsPerfect X := Group.isPerfect_def.mpr hq.1
  refine CFSG.RankThree.PartTwo.KFacts.KS14.eq_bot_of_isPerfect_of_not_sq_dvd
    (Z := Subgroup.center X) le_rfl ?_
  intro p hp hpZ
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpZ)
  exact s15k_schur2_not_sq_dvd hY hp hp2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

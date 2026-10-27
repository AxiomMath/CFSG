module

public import CFSG.RankThree.PartOne.SEITZU49.FourGen
public import CFSG.RankThree.PartOne.SEITZU49.Gen

public section

namespace CFSG.RankThree.PartOne.SEITZU49

open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.RankThree.PartOne.CTP.U5Four

theorem gen49Four_holds : Gen49Four := by
  intro K _ _ _ hK z hz hnz M hM
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hz5 : z ^ 5 = 1 := by
    rw [sigma_apply] at hz
    linear_combination hz
  have hz1 : z ≠ 1 := by
    intro h
    exact hnz ⟨1, by rw [map_one, one_mul], by rw [h]; norm_num⟩
  have hω : z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0 := by
    have : (z - 1) * (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) = 0 := by linear_combination hz5
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hz1
    · exact h
  have hY := Four.Yk_mem_Cset hK hω hM
  rw [Four.Yk_eq] at hY
  have hwσ : unitaryInvolution K 2 2 (val z ![1, 0, 1, 1]) = val z ![1, 0, 1, 1] := by
    have := val_gconj hω (unitaryInvolution K 2 2) (sigma_omega z) ![1, 0, 1, 1]
    rw [Four.check_c1_conj] at this
    exact this.symm
  exact Gen.eq_top_of_Y_mem_Cset hK (by norm_num) hz hM hwσ hY

end CFSG.RankThree.PartOne.SEITZU49

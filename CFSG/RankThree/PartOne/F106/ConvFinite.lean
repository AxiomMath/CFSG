module

public import CFSG.RankThree.PartOne.F106.ConvTwoAdic
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Timmesfeld.Orders CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143
  CFSG.RankThree.PartOne.S12K
open CFSG.RankThree.PartOne.Census3 (sporadicsThm3)
open TauCeti (SporadicName)

@[expose] def sporadicOrder : SporadicName → ℕ
  | .M11 => 7920
  | .M12 => 95040
  | .M22 => 443520
  | .M23 => 10200960
  | .M24 => 244823040
  | .J1 => 175560
  | .J2 => 604800
  | .J3 => 50232960
  | .J4 => 86775571046077562880
  | .McL => 898128000
  | .Ly => 51765179004000000
  | .HS => 44352000
  | .He => 4030387200
  | .Suz => 448345497600
  | .Ru => 145926144000
  | .ONan => 460815505920
  | .Co3 => 495766656000
  | .Co2 => 42305421312000
  | .HN => 273030912000000
  | .Th => 90745943887872000
  | _ => 0

@[expose] def FiniteListOrder (m : ℕ) : Prop :=
  m = 27 ^ 3 * (27 ^ 3 + 1) * 26 ∨ (∃ n, 5 ≤ n ∧ n ≤ 12 ∧ m = n.factorial / 2) ∨
    ∃ s ∈ sporadicsThm3, m = sporadicOrder s

theorem not_two_pow_twenty_dvd {m : ℕ} (hm : FiniteListOrder m) (hJ : m ≠ sporadicOrder .J4) :
    ¬ 2 ^ 20 ∣ m := by
  rcases hm with rfl | ⟨n, h5, h12, rfl⟩ | ⟨s, hs, rfl⟩
  · decide
  · interval_cases n <;> decide
  · simp only [sporadicsThm3, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact absurd rfl hJ | decide

theorem smallEvenParams_of_finiteListOrder {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (hm : FiniteListOrder (charTwoOrder t n f)) :
    SmallEvenParams t n f := by
  by_contra hns
  obtain ⟨N, r, hr, hc, h20, -, h21⟩ := twoAdic_of_nonSmall hadm hns
  by_cases hJ : charTwoOrder t n f = sporadicOrder .J4
  · have hodd : Odd 41377816699065 := by decide
    have hJ4 : sporadicOrder .J4 = 2 ^ 21 * 41377816699065 := by decide
    have hN : 21 = N := eq_of_two_pow_mul_odd hodd hr (hJ4.symm.trans (hJ.symm.trans hc))
    obtain ⟨rfl, rfl, rfl⟩ := h21 hN.symm
    revert hJ
    decide +kernel
  · exact not_two_pow_twenty_dvd hm hJ (hc ▸ Dvd.dvd.mul_right (pow_dvd_pow 2 h20) r)

end CFSG.RankThree.PartOne.F106

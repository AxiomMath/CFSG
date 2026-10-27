module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.RootSubgroupBasic

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem not_commute_of_orderOf_eq_three (hD : IsRootInvolutionSet D) {y c : G} (hy : y ∈ D)
    (hc : c ∈ D) (h3 : orderOf (y * c) = 3) : ¬ Commute y c := fun h => by
  have := orderOf_dvd_of_pow_eq_one
    ((commute_iff_mul_sq_eq_one (hD.mul_self_eq_one hy) (hD.mul_self_eq_one hc)).1 h)
  rw [h3] at this
  exact absurd this (by decide)

theorem odd_of_not_commute_of_ne_four (hD : IsRootInvolutionSet D) {u c : G} (hu : u ∈ D)
    (hc : c ∈ D) (huc : ¬ Commute u c) (h4 : orderOf (u * c) ≠ 4) : Odd (orderOf (u * c)) := by
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hu hc with h | h | ⟨h, -⟩
  · exact absurd h huc
  · exact absurd h h4
  · exact h

end CFSG.Timmesfeld.Moufang

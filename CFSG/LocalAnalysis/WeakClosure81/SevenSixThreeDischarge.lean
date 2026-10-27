module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeRel
public import CFSG.LocalAnalysis.WeakClosure81.ThirteenFour
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement


theorem sevenSixThree_holds : SevenSixThree := by
  intro G _ _ V hV H E J A Y p hp hp2 hEH hEnorm hE hIJ hJ hJnorm hA hAH hJA hJY hYH hAY hYA
    hfaith hexp hcl
  exact seven_six_three_rel hV.1 hV.2.2 hp hp2 hE hEH hEnorm hJ hJnorm hIJ hA hAH hJA hJY hYH
    hAY hYA hfaith hexp hcl

theorem sevenSixThreeAbelian_holds {G : Type} [Group G] [Finite G] (V : Subgroup G) :
    SevenSixThreeAbelian V := by
  intro hV H E J A Y p hp hp2 hEH hEnorm hE hIJ hJ hJnorm hA hAH hJA hJY hYH hAY hYA hfaith hexp
    hab
  have hHnormJ : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal (hJY.trans hYH) hJnorm
  rcases seven_six_three_rel hV.1 hV.2.2 hp hp2 hE hEH hEnorm hJ hJnorm hIJ hA hAH hJA hJY hYH
    hAY hYA hfaith hexp (fun x hx y hy z hz => by
      have hxy : ⁅x, y⁆ ∈ J := hab x hx y hy
      have hconj : z * ⁅x, y⁆⁻¹ * z⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp (hHnormJ (hYH hz)) _).mp (J.inv_mem hxy)
      rw [commutatorElement_def]
      rw [show ⁅x, y⁆ * z * ⁅x, y⁆⁻¹ * z⁻¹ = ⁅x, y⁆ * (z * ⁅x, y⁆⁻¹ * z⁻¹) by group]
      exact J.mul_mem hxy hconj) with h | ⟨-, y, hy, z, hz, hnot⟩
  · exact h
  · exact absurd (hab y hy z hz) hnot

end CFSG.LocalAnalysis.WeakClosure81

module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostNineData
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The selected prime divides the inverted factor `K` because its chosen
order-`p` subgroup `P₀` lies in `K₀ ≤ K`. -/
public theorem secondCase_linear_p_dvd_Kinv
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    {K : Type u} [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K) :
    post.od.p ∣ Nat.card post.equation9.Kinv := by
  have hP0leK : post.od.P0 ≤ post.od.K := by
    have hP0leK0 := post.od.P0_le_K0
    rw [post.od.K0_eq] at hP0leK0
    exact hP0leK0.trans inf_le_right
  have hpdiv : post.od.p ∣ Nat.card post.od.K := by
    rw [← post.od.P0_card]
    exact Subgroup.card_dvd_of_le hP0leK
  rwa [post.equation9_Kinv]

end CFSG.GorensteinWalter

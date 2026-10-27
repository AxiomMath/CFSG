module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralLiftStructure

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

variable {G : Type*} [Group G]

theorem central_involution_intersection_eq_bot_of_odd_center (L : Subgroup G)
    (x : Subgroup.center G) (horder : orderOf (x : G) = 2)
    (hodd : Odd (Nat.card (Subgroup.center L))) :
    L ⊓ centralLiftKernel x = ⊥ := by
  apply (L ⊓ centralLiftKernel x).eq_bot_iff_forall.mpr
  intro a ha
  have hcenter : (⟨a, ha.1⟩ : L) ∈ Subgroup.center L := by
    apply Subgroup.mem_center_iff.mpr
    intro b
    exact Subtype.ext (Subgroup.mem_center_iff.mp
      (centralLiftKernel_le_center x ha.2) b.val)
  have hdivodd : orderOf a ∣ Nat.card (Subgroup.center L) := by
    simpa only [Subgroup.orderOf_mk] using
      (Subgroup.center L).orderOf_dvd_natCard hcenter
  have hdivtwo : orderOf a ∣ 2 := by
    rw [← centralLiftKernel_card_two x horder]
    exact (centralLiftKernel x).orderOf_dvd_natCard ha.2
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hodd) hdivodd hdivtwo)

theorem central_involution_restriction_ker_eq_bot_of_odd_center (L : Subgroup G)
    (x : Subgroup.center G) (horder : orderOf (x : G) = 2)
    (hodd : Odd (Nat.card (Subgroup.center L))) :
    ((QuotientGroup.mk' (centralLiftKernel x)).subgroupMap L).ker = ⊥ := by
  rw [central_lift_subgroup_map_kernel, QuotientGroup.ker_mk',
    Subgroup.subgroupOf_eq_bot]
  exact disjoint_iff.mpr (by
    rw [inf_comm]
    exact central_involution_intersection_eq_bot_of_odd_center L x horder hodd)

@[expose] def centralInvolutionHullEquivOfOddCenter (L : Subgroup G)
    (x : Subgroup.center G) (horder : orderOf (x : G) = 2)
    (hodd : Odd (Nat.card (Subgroup.center L))) :
    L ≃* L.map (QuotientGroup.mk' (centralLiftKernel x)) :=
  MulEquiv.ofBijective ((QuotientGroup.mk' (centralLiftKernel x)).subgroupMap L)
    ⟨((QuotientGroup.mk' (centralLiftKernel x)).subgroupMap L).ker_eq_bot_iff.mp
      (central_involution_restriction_ker_eq_bot_of_odd_center L x horder hodd),
      (QuotientGroup.mk' (centralLiftKernel x)).subgroupMap_surjective L⟩

theorem centralInvolutionHullEquivOfOddCenter_apply (L : Subgroup G)
    (x : Subgroup.center G) (horder : orderOf (x : G) = 2)
    (hodd : Odd (Nat.card (Subgroup.center L))) (a : L) :
    (centralInvolutionHullEquivOfOddCenter L x horder hodd a :
      G ⧸ centralLiftKernel x) = QuotientGroup.mk' (centralLiftKernel x) (a : G) :=
  rfl

end CFSG.ShultStronglyClosedTI

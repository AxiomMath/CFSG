module

public import CFSG.Timmesfeld.Bridge.RootStructR2KOneBender

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.GH74.Uniqueness.Bender CFSG.Timmesfeld.Bridge.RootKOne

theorem rootGroup_eq_sylowCenter_of_isBenderGroup {K : Type}
    [Group K] [Finite K] {D : Set K} (hS : CFSG.Timmesfeld.Bridge.Asc72.Setup K D)
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) {d : K} (hd : d ∈ D) :
    ∃ T : Sylow 2 K, d ∈ (T : Subgroup K) ∧
      CFSG.Timmesfeld.rootGroup D d =
        (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) := by
  obtain ⟨n, i, e, hBT⟩ := isBenderGroup_iff_exists_benderType.mp hK
  have hd1 : d ≠ 1 := hS.oddT.ne_one hd
  have hd2 : d * d = 1 := hS.oddT.mul_self_eq_one hd
  have hdord : orderOf d = 2 := hS.oddT.orderOf_eq_two hd
  have hp : IsPGroup 2 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hdord, pow_one])
  obtain ⟨T, hdT⟩ := hp.exists_le_sylow
  have hdT' : d ∈ (T : Subgroup K) := hdT (Subgroup.mem_zpowers d)
  refine ⟨T, hdT', le_antisymm ?_ ?_⟩
  · rw [CFSG.Timmesfeld.rootGroup]
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hx1 : x ≠ 1 := hS.oddT.ne_one hx.1
    have hx2 : x * x = 1 := hS.oddT.mul_self_eq_one hx.1
    have hcomm : Commute d x := ((hx.2 d hd).2 (Commute.refl d)).symm
    exact mem_rootCenter_of_commute hBT T hdT' hd1 hd2 hx1 hx2 hcomm
  · intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact (CFSG.Timmesfeld.rootGroup D d).one_mem
    · refine Subgroup.subset_closure ?_
      rw [CFSG.Timmesfeld.mem_rootSet_iff hS.isClass hd]
      have hzZ : z ∈ rootCenter (T : Subgroup K) := hz
      have hzT : z ∈ (T : Subgroup K) := (Subgroup.mem_inf.mp hz).1
      have hzC : z ∈ Subgroup.centralizer ((T : Subgroup K) : Set K) :=
        (Subgroup.mem_inf.mp hz).2
      have hz2 : z * z = 1 := mul_self_eq_one_of_mem_rootCenter hBT T hzZ
      have hzord : orderOf z = 2 := orderOf_eq_prime (by rwa [pow_two]) hz1
      refine ⟨?_, ?_, ?_⟩
      · rw [hS.eq_setOf_isConj hd]
        exact CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hK
          hdord hzord
      · exact Subgroup.mem_centralizer_iff.mp hzC d hdT'
      · intro f hf hdf
        have hf1 : f ≠ 1 := hS.oddT.ne_one hf
        have hf2 : f * f = 1 := hS.oddT.mul_self_eq_one hf
        have hfZ : f ∈ rootCenter (T : Subgroup K) :=
          mem_rootCenter_of_commute hBT T hdT' hd1 hd2 hf1 hf2 hdf
        have hfC : f ∈ Subgroup.centralizer ((T : Subgroup K) : Set K) :=
          (Subgroup.mem_inf.mp hfZ).2
        exact Subgroup.mem_centralizer_iff.mp hfC z hzT

theorem mem_of_mem_rootGroup_of_isBenderGroup {K : Type}
    [Group K] [Finite K] {D : Set K} (hS : CFSG.Timmesfeld.Bridge.Asc72.Setup K D)
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) {d : K} (hd : d ∈ D) {z : K}
    (hz : z ∈ CFSG.Timmesfeld.rootGroup D d) (hz1 : z ≠ 1) : z ∈ D := by
  obtain ⟨n, i, e, hBT⟩ := isBenderGroup_iff_exists_benderType.mp hK
  obtain ⟨T, -, hroot⟩ := rootGroup_eq_sylowCenter_of_isBenderGroup hS hK hd
  have hzZ : z ∈ rootCenter (T : Subgroup K) := by
    change z ∈ (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K)
    rw [← hroot]
    exact hz
  have hz2 : z * z = 1 := mul_self_eq_one_of_mem_rootCenter hBT T hzZ
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rwa [pow_two]) hz1
  have hdord : orderOf d = 2 := hS.oddT.orderOf_eq_two hd
  rw [hS.eq_setOf_isConj hd]
  exact CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isConj_of_orderOf_eq_two hK hdord hzord

end CFSG.LocalAnalysis.WeakClosure81.TimTI

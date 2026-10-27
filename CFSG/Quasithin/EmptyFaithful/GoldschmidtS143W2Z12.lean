module

public import CFSG.Quasithin.EmptyFaithful.S143UE

public section

namespace CFSG.Quasithin

open scoped MatrixGroups

namespace S143

namespace InspW2

theorem sl23_order_three : ∃ t : SL(2, ZMod 3), orderOf t = 3 := by
  have h : ∃ t : SL(2, ZMod 3), t ^ 3 = 1 ∧ t ≠ 1 := by decide +kernel
  obtain ⟨t, h3, h1⟩ := h
  exact ⟨t, orderOf_eq_prime h3 h1⟩

theorem exists_orderOf_twelve_of_z4StarSL23 {P : Type*} [Group P] (hP : IsZ4StarSL23 P) :
    ∃ g : P, orderOf g = 12 := by
  obtain ⟨-, A, B, ⟨hAB, -⟩, hA4, hAcyc, ⟨eB⟩⟩ := hP
  obtain ⟨t, ht⟩ := sl23_order_three
  obtain ⟨c, hc⟩ := hAcyc.exists_generator
  have hcord : orderOf c = 4 := by rw [orderOf_eq_card_of_forall_mem_zpowers hc, hA4]
  have hcP : orderOf (c : P) = 4 := by rw [Subgroup.orderOf_coe, hcord]
  have hbord : orderOf ((eB.symm t : ↥B) : P) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  have hcomm : Commute (c : P) ((eB.symm t : ↥B) : P) :=
    ((Subgroup.mem_centralizer_iff.mp (hAB c.2) _ (eB.symm t).2)).symm
  refine ⟨(c : P) * ((eB.symm t : ↥B) : P), ?_⟩
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hcP, hbord]; norm_num), hcP, hbord]

end InspW2

end S143

end CFSG.Quasithin

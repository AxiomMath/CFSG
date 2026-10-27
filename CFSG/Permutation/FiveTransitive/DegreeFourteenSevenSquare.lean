module

public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan

public section

namespace CFSG

namespace FiveTransitive.DegreeFourteenSevenSquare
open MulAction

private theorem exists_seven_cycle
    {E : Type*} [Fintype E] [DecidableEq E]
    (B : Subgroup (Equiv.Perm E)) [IsPretransitive B E]
    (hE : Nat.card E = 14) (hB : 49 ∣ Nat.card B) :
    ∃ g : Equiv.Perm E, g ∈ B ∧ g.IsCycle ∧ g.support.card = 7 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : Nonempty E := Finite.card_pos_iff.mp (by omega)
  let x : E := Classical.choice inferInstance
  have hm := (stabilizer B x).index_mul_card
  rw [index_stabilizer_of_transitive,hE] at hm
  have hs : 7 ∣ Nat.card (stabilizer B x) := by omega
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := stabilizer B x) 7 hs
  let g : Equiv.Perm E := u.val.val
  have hg : orderOf g = 7 :=
    (Subgroup.orderOf_coe u.val).trans ((Subgroup.orderOf_coe u).trans hu)
  have hx : g x = x := u.property
  have hsub : g.support ⊆ Finset.univ.erase x :=
    Finset.subset_erase.mpr ⟨Finset.subset_univ _,Equiv.Perm.notMem_support.mpr hx⟩
  have hb := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ,
    ← Nat.card_eq_fintype_card,hE] at hb
  have hc : g.IsCycle := Equiv.Perm.isCycle_of_prime_order
    (by rw [hg]; decide) (by rw [hg]; omega)
  exact ⟨g,u.val.property,hc,hc.orderOf.symm.trans hg⟩

theorem alternating_le
    {E : Type*} [Fintype E] [DecidableEq E]
    (B : Subgroup (Equiv.Perm E)) (hprim : IsPreprimitive B E)
    (hE : Nat.card E = 14) (hB : 49 ∣ Nat.card B) : alternatingGroup E ≤ B := by
  let _ : IsPreprimitive B E := hprim
  obtain ⟨g,hg,hcycle,hsupport⟩ := exists_seven_cycle B hE hB
  exact OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    hprim (by decide : Nat.Prime 7) (by omega) hcycle hsupport hg

end FiveTransitive.DegreeFourteenSevenSquare

end CFSG

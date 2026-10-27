module

public import CFSG.Permutation.FiveTransitive.LargePrimeCyclePrimitive
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFactorial

public section

namespace CFSG

namespace FiveTransitive.NineDegreeOrderObstruction
open MulAction

private theorem stabilizer_card_dvd
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (x : X) :
    Nat.card (stabilizer P x) ∣ (Nat.card X - 1).factorial := by
  classical
  let H := stabilizer P x
  let Y := SubMulAction.ofStabilizer P x
  have hi : Function.Injective (MulAction.toPermHom H Y) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro y
    by_cases hy : y = x
    · subst y
      exact (mem_stabilizer_iff.mp a.property).trans (mem_stabilizer_iff.mp b.property).symm
    · have hyY : y ∈ SubMulAction.ofStabilizer P x := hy
      have he := congrArg (fun e : Equiv.Perm Y => (e ⟨y,hyY⟩).val) hab
      exact he
  have hd := Subgroup.card_dvd_of_injective (MulAction.toPermHom H Y) hi
  rw [Nat.card_perm, SubMulAction.nat_card_ofStabilizer_eq] at hd
  exact hd

private theorem transitive_of_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hX : Nat.card X = 9)
    (hP : Nat.card P = 12960) : IsPretransitive P X := by
  classical
  constructor
  intro x y
  let : Fintype (orbit P x) := Fintype.ofFinite _
  let : Fintype (stabilizer P x) := Fintype.ofFinite _
  have hm := card_orbit_mul_card_stabilizer_eq_card_group P x
  simp only [← Nat.card_eq_fintype_card] at hm
  have hd := Nat.mul_dvd_mul_left (Nat.card (orbit P x)) (stabilizer_card_dvd P x)
  rw [hm,hP,hX] at hd
  have ho : Nat.card (orbit P x) ≤ 9 := by
    rw [← hX]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have he : Nat.card (orbit P x) = 9 := by
    generalize Nat.card (orbit P x) = o at *
    rw [hP] at hm
    interval_cases o <;> norm_num at hd <;> omega
  have hall : orbit P x = Set.univ := (Set.eq_univ_iff_ncard _).mpr (by rw [← Nat.card_coe_set_eq]; exact he.trans hX.symm)
  exact mem_orbit_iff.mp (hall ▸ Set.mem_univ y)

theorem card_ne
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hX : Nat.card X = 9) :
    Nat.card P ≠ 12960 := by
  intro hP
  let _ : IsPretransitive P X := transitive_of_card P hX hP
  have hd : 5 ∣ Nat.card P := by rw [hP]; norm_num
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' 5 hd
  have hg : orderOf (u : Equiv.Perm X) = 5 := (Subgroup.orderOf_coe u).trans hu
  have hc : (u : Equiv.Perm X).IsCycle := Equiv.Perm.isCycle_of_prime_order
    (by rw [hg]; norm_num) (by rw [hg]; exact lt_of_le_of_lt (Finset.card_le_univ _) (by simp [← Nat.card_eq_fintype_card,hX]))
  have hs : (u : Equiv.Perm X).support.card = 5 := hc.orderOf.symm.trans hg
  have hp : IsPreprimitive P X := LargePrimeCyclePrimitive.isPreprimitive P u.property hc
    (by rw [hs]; norm_num) (by rw [hX,hs]; norm_num)
  have halt := OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    hp (by norm_num : Nat.Prime 5) (by rw [hX]; norm_num) hc hs u.property
  have hd := Subgroup.card_dvd_of_le halt
  let _ : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  rw [nat_card_alternatingGroup,hX,hP] at hd
  norm_num at hd

end FiveTransitive.NineDegreeOrderObstruction

end CFSG

module

public import CFSG.RankThree.GF2n.Tim78Normal
public import CFSG.RankThree.GF2n.Tim78Involution

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78

variable {G : Type} [Group G]

structure Hyp3 (M V Q P : Subgroup G) : Prop where
  o2 : pCore 2 G = ⊥
  maxLocal : IsMaximalTwoLocal M
  fitting : generalizedFitting M = pCore 2 M
  maxAb : Maximal (fun U : Subgroup G => U ≤ M ∧ M ≤ Subgroup.normalizer (U : Set G) ∧
    IsMulCommutative U) V
  elemAb : Assembly.IsElemAbelian 2 V
  ti : IsTI V
  four : 4 ≤ Nat.card V
  hQ : Q = inSubgroup (pCore 2) M
  hP : P = Q ⊓ Subgroup.centralizer (V : Set G)

namespace Hyp3

variable [Finite G] {M V Q P : Subgroup G} (H : Hyp3 M V Q P)
include H

omit [Finite G] in
theorem V_le_M : V ≤ M := H.maxAb.prop.1

omit [Finite G] in
theorem M_le_normalizer_V : M ≤ Subgroup.normalizer (V : Set G) := H.maxAb.prop.2.1

omit [Finite G] in
theorem isPGroup_V : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using H.elemAb.2 x x.2)⟩

omit [Finite G] in
theorem V_ne_bot : V ≠ ⊥ := by
  intro h
  have := H.four
  rw [h, Subgroup.card_bot] at this
  omega

omit [Finite G] in
theorem isPGroup_Q : IsPGroup 2 Q := H.hQ ▸ (inSubgroup_pCore_two M).1

omit [Finite G] in
theorem M_le_normalizer_Q : M ≤ Subgroup.normalizer (Q : Set G) :=
  H.hQ ▸ (inSubgroup_pCore_two M).2.2

omit [Finite G] in
theorem V_le_Q : V ≤ Q :=
  H.hQ ▸ le_inSubgroup_pCore H.V_le_M H.M_le_normalizer_V H.isPGroup_V

omit [Finite G] in
theorem P_le_Q : P ≤ Q := H.hP ▸ inf_le_left

omit [Finite G] in
theorem isPGroup_P : IsPGroup 2 P := H.isPGroup_Q.to_le H.P_le_Q

omit [Finite G] in
theorem center_P {b x : G} (hb : b ∈ V) (hx : x ∈ P) : b * x = x * b := by
  have : x ∈ Subgroup.centralizer (V : Set G) := (H.hP ▸ hx : x ∈ Q ⊓ _).2
  exact Subgroup.mem_centralizer_iff.mp this b hb

omit [Finite G] in
theorem V_le_P : V ≤ P := by
  rw [H.hP]
  refine le_inf H.V_le_Q fun v hv => Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  exact comm_of_isElemAbelian H.elemAb ha hv

end Hyp3

end CFSG.RankThree.GF2n.Tim81

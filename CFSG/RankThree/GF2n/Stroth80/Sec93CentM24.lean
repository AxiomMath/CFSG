module

public import CFSG.CGT.Timmesfeld75.ListWCCert
public import CFSG.Quasithin.AppendixH.H14.M24InvolutionClasses
public import CFSG.RankThree.GF2n.Stroth80.Sec93CentFixedPoints

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Monster.Code
open CFSG.ASVolI.ChH

theorem m24_orderOf_two_of_involution {x : ↥CFSG.Monster.Code.AutPerm} (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : orderOf (x : Equiv.Perm (Fin 24)) = 2 := by
  have h2 : (x : Equiv.Perm (Fin 24)) ^ 2 = 1 := by
    rw [pow_two, ← Subgroup.coe_mul, hx2, Subgroup.coe_one]
  have h1 : (x : Equiv.Perm (Fin 24)) ≠ 1 := fun h =>
    hx1 (Subtype.ext (by simpa using h))
  exact orderOf_eq_prime h2 h1

theorem m24_card_fixed_eq_zero {x : Equiv.Perm (Fin 24)} (h : ∀ i, x i ≠ i) :
    Nat.card {i : Fin 24 // x i = i} = 0 := by
  have : IsEmpty {i : Fin 24 // x i = i} := ⟨fun i => h i.1 i.2⟩
  exact Nat.card_of_isEmpty

theorem m24_isTwoCentralElt_of_card_ne_zero
    {x : ↥CFSG.Monster.Code.AutPerm} (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx : Nat.card {i : Fin 24 // (x : Equiv.Perm (Fin 24)) i = i} ≠ 0) :
    IsTwoCentralElt M24g (x : Equiv.Perm (Fin 24)) := by
  by_contra hc
  have hxM : (x : Equiv.Perm (Fin 24)) ∈ M24g := x.2
  exact hx (m24_card_fixed_eq_zero
    ((CFSG.Quasithin.AppendixH.H14.m24_involution_classes.1 (x : Equiv.Perm (Fin 24)) hxM
      (m24_orderOf_two_of_involution hx2 hx1)).2.mp hc))

theorem m24_fixed_card_of_involution
    {z : ↥CFSG.Monster.Code.AutPerm} (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card {i : Fin 24 // (z : Equiv.Perm (Fin 24)) i = i} = 8 ∨
      Nat.card {i : Fin 24 // (z : Equiv.Perm (Fin 24)) i = i} = 0 := by
  have hzM : (z : Equiv.Perm (Fin 24)) ∈ M24g := z.2
  have hcls := CFSG.Quasithin.AppendixH.H14.m24_involution_classes.1
    (z : Equiv.Perm (Fin 24)) hzM (m24_orderOf_two_of_involution hz2 hz1)
  by_cases hc : IsTwoCentralElt M24g (z : Equiv.Perm (Fin 24))
  · obtain ⟨O, hO, hOiff⟩ := hcls.1.mp hc
    have e : {i : Fin 24 // (z : Equiv.Perm (Fin 24)) i = i} ≃ {i : Fin 24 // i ∈ O} :=
      Equiv.subtypeEquivRight fun i => (hOiff i).symm
    left
    rw [Nat.card_congr e, Nat.card_eq_finsetCard, hO.1]
  · right
    exact m24_card_fixed_eq_zero (hcls.2.mp hc)

theorem m24_isConj_of_fixed_card_eight
    {z w : ↥CFSG.Monster.Code.AutPerm} (hz2 : z * z = 1) (hz1 : z ≠ 1) (hw2 : w * w = 1)
    (hw1 : w ≠ 1)
    (hz8 : Nat.card {i : Fin 24 // (z : Equiv.Perm (Fin 24)) i = i} = 8)
    (hw8 : Nat.card {i : Fin 24 // (w : Equiv.Perm (Fin 24)) i = i} = 8) : IsConj z w := by
  have hzc := m24_isTwoCentralElt_of_card_ne_zero hz2 hz1 (by rw [hz8]; norm_num)
  have hwc := m24_isTwoCentralElt_of_card_ne_zero hw2 hw1 (by rw [hw8]; norm_num)
  obtain ⟨g, hg, hgeq⟩ := CFSG.Quasithin.AppendixH.H14.m24_involution_classes.2.2.2.1
    (z : Equiv.Perm (Fin 24)) z.2 (w : Equiv.Perm (Fin 24)) w.2
    (m24_orderOf_two_of_involution hz2 hz1) (m24_orderOf_two_of_involution hw2 hw1) hzc hwc
  exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext hgeq⟩

noncomputable def nativeM24EquivAutPerm :
    ↥CFSG.Blueprint.NativeSporadic.M24 ≃* ↥AutPerm :=
  (CFSG.Blueprint.NativeSporadic.M24.equivMapOfInjective _
      (MulAut.conj bridgeQ⁻¹).injective).trans
    (MulEquiv.subgroupCongr (AutPerm_eq_closure.trans bridge_closure_eq_map)).symm

theorem wcOrderConj_autPerm :
    WCOrderConj ↥AutPerm 16 :=
  (wcOrderConj_m24 m24WCCheck_holds).of_mulEquiv nativeM24EquivAutPerm.symm

theorem mem_of_mul_self_eq_one_autPerm
    {T : Subgroup ↥AutPerm} (hT : IsWC T) (h4 : 4 ≤ Nat.card T)
    {x : ↥AutPerm} (hx : x ∈ Subgroup.centralizer (T : Set ↥AutPerm)) (hx2 : x * x = 1) :
    x ∈ T := by
  obtain ⟨hcard, hconj⟩ := wcOrderConj_autPerm T hT h4
  exact mem_of_mul_self_eq_one_of_fixedPoints AutPerm.subtype hT (m := 4) (N := 24) (a := 8)
    (by norm_num) (by rw [hcard]; norm_num) hconj
    (fun z hz2 hz1 => m24_fixed_card_of_involution hz2 hz1)
    (fun z w hz2 hz1 hw2 hw1 hz8 hw8 => m24_isConj_of_fixed_card_eight hz2 hz1 hw2 hw1 hz8 hw8)
    (by simp) (by norm_num) (by norm_num) hx hx2

theorem mem_of_mul_self_eq_one_m24
    {S : Type} [Group S] (hS : CFSG.Blueprint.NativeSporadic.IsSporadic S .M24) {T : Subgroup S}
    (hT : IsWC T) (h4 : 4 ≤ Nat.card T) {x : S} (hx : x ∈ Subgroup.centralizer (T : Set S))
    (hx2 : x * x = 1) : x ∈ T := by
  obtain ⟨e⟩ : Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.M24) := hS
  exact mem_of_mul_self_eq_one_of_mulEquiv (e.trans nativeM24EquivAutPerm)
    (fun T' hT' h4' x' hx' hx2' => mem_of_mul_self_eq_one_autPerm hT' h4' hx' hx2') hT h4 hx hx2

end CFSG.RankThree.GF2n.Stroth80

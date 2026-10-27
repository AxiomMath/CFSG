module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusDefs
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeZQ

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusPerfect
import CFSG.RankThree.GF2n.Stroth78.Sec2SixteenReverse
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem card_ZQ_inf_QaOf_eq (S : Setting z E F) (a : G) :
    Nat.card (ZQ z ⊓ QaOf a : Subgroup G) = Nat.card ↥((ZQ z).subgroupOf (QaOf a)) := by
  rw [← Subgroup.inf_subgroupOf_right (ZQ z) (QaOf a)]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_right : ZQ z ⊓ QaOf a ≤ QaOf a)).toEquiv).symm

theorem card_Rbar_eq_two_of_card_ZQ_eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hZ : Nat.card ↥(ZQ z) = 4) : Nat.card ↥(Rbar S a) = 2 := by
  have hcard := card_ZQ_eq S h
  rw [hZ] at hcard
  have hz1 : z ≠ 1 := by
    intro hz
    have := S.hyp.orderOf_z
    rw [hz, orderOf_one] at this
    omega
  have hR1 : Nat.card ↥(Rbar S a) ≠ 1 := fun h1 =>
    h.Rbar_ne_bot (Subgroup.card_eq_one.mp h1)
  have hK1 : Nat.card ↥((ZQ z).subgroupOf (QaOf a)) ≠ 1 := by
    intro h1
    have hzK : (⟨z, h.mem_Qa⟩ : ↥(QaOf a)) ∈ (ZQ z).subgroupOf (QaOf a) :=
      Subgroup.mem_subgroupOf.mpr (z_mem_ZQ S)
    rw [Subgroup.card_eq_one.mp h1, Subgroup.mem_bot] at hzK
    exact hz1 (congrArg Subtype.val hzK)
  have hRpos : 0 < Nat.card ↥(Rbar S a) := Nat.card_pos
  have hKpos : 0 < Nat.card ↥((ZQ z).subgroupOf (QaOf a)) := Nat.card_pos
  generalize Nat.card ↥(Rbar S a) = r at *
  generalize Nat.card ↥((ZQ z).subgroupOf (QaOf a)) = k at *
  have hr2 : 2 ≤ r := by omega
  have hk2 : 2 ≤ k := by omega
  have hr : r ≤ 2 := by nlinarith
  omega

theorem ZQ_inf_QaOf_eq_zpowers_of_card_ZQ_eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hZ : Nat.card ↥(ZQ z) = 4) :
    ZQ z ⊓ QaOf a = Subgroup.zpowers z := by
  have hR := card_Rbar_eq_two_of_card_ZQ_eq_four S h hZ
  have hcard := card_ZQ_eq S h
  rw [hZ, hR] at hcard
  have hk : Nat.card ↥((ZQ z).subgroupOf (QaOf a)) = 2 := by omega
  have hle : Subgroup.zpowers z ≤ ZQ z ⊓ QaOf a :=
    (Subgroup.zpowers_le).mpr (Subgroup.mem_inf.mpr ⟨z_mem_ZQ S, h.mem_Qa⟩)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_ZQ_inf_QaOf_eq S a, hk, Nat.card_zpowers, S.hyp.orderOf_z]

theorem centerIn_QaOf_inf_Q_eq_zpowers_of_card_ZQ_eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (hZ : Nat.card ↥(ZQ z) = 4) :
    centerIn (QaOf a) ⊓ Q z = Subgroup.zpowers a := by
  have hR := card_Rbar_eq_two_of_card_ZQ_eq_four S h hZ
  have hcount := card_Rbar_mul_card_inf_Q_of_mem S h.mem_Qa
  rw [card_centerIn_QaOf_eq_card_ZQ S h.isConj, hZ, hR] at hcount
  have hk : Nat.card ↥(centerIn (QaOf a) ⊓ Q z : Subgroup G) = 2 := by omega
  have ha1 : a ≠ 1 := fun ha => h.not_mem_ZQ (ha ▸ (ZQ z).one_mem)
  have ha2 : a ^ 2 = 1 := by
    have := a_mul_self_eq_one S h.isConj
    rwa [← pow_two] at this
  have hao : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hle : Subgroup.zpowers a ≤ centerIn (QaOf a) ⊓ Q z :=
    (Subgroup.zpowers_le).mpr
      (Subgroup.mem_inf.mpr ⟨mem_centerIn_QaOf_of_isConj S h.isConj, h.mem_Q⟩)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hk, Nat.card_zpowers, hao]

theorem rhoZ_eq_self_of_mem_Xsub_of_card_ZQ_eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hZ : Nat.card ↥(ZQ z) = 4) :
    ∀ x ∈ Xsub S a, ∀ u : ↥(ZQ z), rhoZ S x u = u := by
  let ψ : Hbar z →* Equiv.Perm ↥(ZQ z) := (MulAut.toPerm ↥(ZQ z)).comp (rhoZ S)
  haveI : Group.IsSolvable (Equiv.Perm ↥(ZQ z)) := Equiv.Perm.isSolvable (by rw [hZ])
  have hperf := commutator_Xsub_eq_of_threeFourPlus S h h217 h34
  have hY : ⁅(Xsub S a).map ψ, (Xsub S a).map ψ⁆ = (Xsub S a).map ψ := by
    rw [← Subgroup.map_commutator, hperf]
  have hYbot : (Xsub S a).map ψ = ⊥ := by
    by_contra hne
    exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne hY
  intro x hx u
  have hx1 : ψ x = 1 := by
    have hmem : ψ x ∈ (Xsub S a).map ψ := Subgroup.mem_map_of_mem ψ hx
    rw [hYbot, Subgroup.mem_bot] at hmem
    exact hmem
  have := congrArg (fun p : Equiv.Perm ↥(ZQ z) => p u) hx1
  exact this

end CFSG.RankThree.GF2n.Stroth78

module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusDefs

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusZQFour
import CFSG.LargeExtraspecial.AS35QCoLin
import CFSG.RankThree.GF2n.Stroth78.Sec3Three
import CFSG.RankThree.GF2n.Stroth78.Sec2SixteenReverse
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.GroupTheory.AutAlt8Bound
public import CFSG.RankThree.GF2n.Stroth78.Sec2QaAbelian
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem card_Lbar_numerics_of_mulEquiv_alt8 (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hZ : Nat.card ↥(ZQ z) = 4)
    (e : ↥(Xsub S a) ≃* alternatingGroup (Fin 8)) :
    w ≤ 5 ∧ Nat.card ↥(Lbar S a) * Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) = 2 ^ (2 * w) ∧
      Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) ≤ 2 ^ w ∧
      Nat.card ↥(Lbar S a) ≤
        16 * Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) ∧
      Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) ≤ 2 := by
  classical
  letI := modAbF S
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  haveI hXn : (Xsub S a).Normal := Xsub_normal S a
  have hA : ∀ e ∈ Lbar S a, e * e = 1 := fun e he => by
    rw [← pow_two]
    exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj he
  have hLb := CFSG.GroupTheory.card_le_sixteen_mul_card_inf_centralizer_of_mulEquiv_alt8
    (Xsub S a) e (Lbar S a) hA
  have hC6 := card_centralizer_Xsub_dvd_six S h h217
  set C : Subgroup (Hbar z) := Subgroup.centralizer (Xsub S a : Set (Hbar z)) with hCdef
  have hD2 : Nat.card ↥(Lbar S a ⊓ C) ≤ 2 := by
    have hdvd : Nat.card ↥(Lbar S a ⊓ C) ∣ 6 :=
      (Subgroup.card_dvd_of_le (inf_le_right : Lbar S a ⊓ C ≤ C)).trans hC6
    have h3 : ¬ 3 ∣ Nat.card ↥(Lbar S a ⊓ C) := by
      intro h3
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Lbar S a ⊓ C)) 3 h3
      have hx2 : x * x = 1 := Subtype.ext (hA x (Subgroup.mem_inf.mp x.2).1)
      have hdv : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
      rw [hx] at hdv
      omega
    have hle6 : Nat.card ↥(Lbar S a ⊓ C) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card ↥(Lbar S a ⊓ C) := Nat.card_pos
    generalize Nat.card ↥(Lbar S a ⊓ C) = n at hdvd h3 hle6 hpos ⊢
    interval_cases n <;> omega
  have hR : Nat.card ↥(Rbar S a) = 2 := card_Rbar_eq_two_of_card_ZQ_eq_four S h hZ
  have ha1 : a ≠ 1 := fun ha1 => h.not_mem_ZQ (ha1 ▸ (ZQ z).one_mem)
  have ha2 : a ^ 2 = 1 := by
    have := a_mul_self_eq_one S h.isConj
    rwa [← pow_two] at this
  have hao : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hcard : Nat.card (ZQ z ⊓ QaOf a : Subgroup G) =
      Nat.card (centerIn (QaOf a) ⊓ Q z : Subgroup G) := by
    rw [ZQ_inf_QaOf_eq_zpowers_of_card_ZQ_eq_four S h hZ,
      centerIn_QaOf_inf_Q_eq_zpowers_of_card_ZQ_eq_four S h hZ, Nat.card_zpowers,
      Nat.card_zpowers, S.hyp.orderOf_z, hao]
  have hid := two_mul_card_Lbar_mul_card_QaInterImage_of_card_inf S h.isConj h.mem_Q
    h.not_mem_ZQ h.mem_Qa hcard
  rw [hR, card_QbarOf_eq_pow S h.card_F] at hid
  have hcommB : ∀ x ∈ QaOf a ⊓ Q z, ∀ y ∈ QaOf a ⊓ Q z, x * y = y * x :=
    fun x hx y hy => commute_of_mem_QaOf_inf_Q S h.isConj h.not_mem_ZQ hx hy
  have hIdim := finrank_QaInterImage_le S hcommB h.card_F
  have hIcard : Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) =
      2 ^ finrank (ZMod 2) ↥(QaInterImage S (QaOf a ⊓ Q z)) :=
    CFSG.LargeExtraspecial.AS35QCo.natCard_submodule _
  have hIle : Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) ≤ 2 ^ w := by
    rw [hIcard]
    exact Nat.pow_le_pow_right (by norm_num) hIdim
  have hLi : Nat.card ↥(Lbar S a) * Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) = 2 ^ (2 * w) := by
    linarith
  have hℓ : Nat.card ↥(Lbar S a) ≤ 32 := by omega
  refine ⟨?_, hLi, hIle, hLb, hD2⟩
  have h1 : 2 ^ w * 2 ^ w ≤ 32 * 2 ^ w := by
    calc 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by rw [two_mul, pow_add]
      _ = Nat.card ↥(Lbar S a) * Nat.card ↥(QaInterImage S (QaOf a ⊓ Q z)) := hLi.symm
      _ ≤ 32 * 2 ^ w := Nat.mul_le_mul hℓ hIle
  have h2 : 2 ^ w ≤ 32 := Nat.le_of_mul_le_mul_right h1 (by positivity)
  by_contra hlt
  push Not at hlt
  have : 2 ^ 6 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hlt
  omega

end CFSG.RankThree.GF2n.Stroth78

module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusDefs

import CFSG.LargeExtraspecial.A2ModCentralizerLine
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusTwelveObstruction
import CFSG.GroupTheory.ExistsSubgroupCardLeOfNormalizer
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusTwelveSeven
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusCenter
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusZQFour
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedSq
import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeLift
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem false_of_sylow_three_bound (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hw4 : 4 ≤ w) (hZ : Nat.card ↥(ZQ z) = 4)
    (h7 : 7 ∣ Nat.card ↥(Xsub S a)) (hOut : Nat.card (Outer ↥(Xsub S a)) = 1)
    (hbound : ∀ r ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)),
      ∀ P : Sylow 3 ↥(Subgroup.centralizer ({r} : Set ↥(Xsub S a))),
      ∀ A : Subgroup ↥(Xsub S a), (∀ e ∈ A, e * e = 1) → (∀ e ∈ A, ∀ f ∈ A, e * f = f * e) →
        r ∈ A → (∀ x ∈ A, x * r = r * x) →
        (∀ t : ↥(Subgroup.centralizer ({r} : Set ↥(Xsub S a))), t ∈ P → ∀ x ∈ A,
          (t : ↥(Xsub S a)) * x * (t : ↥(Xsub S a))⁻¹ ∈ A) →
        Nat.card ↥A ≤ 8) : False := by
  classical
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  haveI hXn : (Xsub S a).Normal := Xsub_normal S a
  have hZX0 : Subgroup.center ↥(Xsub S a) = ⊥ := center_Xsub_eq_bot_of_threeFourPlus S h h217 h34
  have hD := rootClass_Xsub S h h217 h34
  have hA := a2Action_Xsub S a
  have hZX := rhoZ_eq_self_of_mem_Xsub_of_card_ZQ_eq_four S h h217 h34 hZ
  have hR2 := card_Rbar_eq_two_of_card_ZQ_eq_four S h hZ
  obtain ⟨⟨α, hαR⟩, hα1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα1 : α ≠ 1 := fun h1 => hα1' (Subtype.ext h1)
  set r : ↥(Xsub S a) := ⟨α, h.Rbar_le_Xsub hαR⟩ with hr
  have hrD : r ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hαR hα1)
  have haL : aVec S h.mem_Q ∈ commSpace (rhoX S a r) :=
    (mem_A2set_and_aVec_mem_of_mem_Rbar h hαR hα1).2
  have haT0 : aVec S h.mem_Q ≠ 0 := aV_ne_zero S h.mem_Q h.not_mem_ZQ
  have hT2 := ncard_conj_fixer_le_two S h hZ hZX hR2 (r := r) hαR hα1
  by_cases htrans : ∀ u ∈ commSpace (rhoX S a r), u ≠ 0 →
      ∃ c : ↥(Xsub S a), c * r = r * c ∧ rhoX S a c (aVec S h.mem_Q) = u
  · exact hD.false_of_transitive hA hrD haT0 haL htrans hT2
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨P⟩ := (inferInstance :
      Nonempty (Sylow 3 ↥(Subgroup.centralizer ({r} : Set ↥(Xsub S a)))))
    set C : Subgroup ↥(Xsub S a) := Subgroup.centralizer ({r} : Set ↥(Xsub S a)) with hC
    set T₀ : Subgroup ↥(Xsub S a) := (P : Subgroup ↥C).map C.subtype with hT₀
    have hTr : ∀ t ∈ T₀, t * r = r * t := by
      rintro _ ⟨t, -, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp t.2
    have hT3 : IsPGroup 3 ↥T₀ :=
      (P.2).of_surjective (Subgroup.equivMapOfInjective (P : Subgroup ↥C) C.subtype
        C.subtype_injective).toMonoidHom (Subgroup.equivMapOfInjective (P : Subgroup ↥C)
          C.subtype C.subtype_injective).surjective
    have hfixT : ∀ t ∈ T₀, rhoX S a t (aVec S h.mem_Q) = aVec S h.mem_Q :=
      hA.fix_of_isPGroup_three hrD haT0 haL htrans T₀ hT3 hTr
    set Y : Subgroup (Hbar z) := T₀.map (Xsub S a).subtype with hY
    have hYfix : ∀ y ∈ Y, rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q := by
      rintro _ ⟨t, ht, rfl⟩
      exact hfixT t ht
    have hYZ : ∀ y ∈ Y, ∀ u : ↥(ZQ z), rhoZ S y u = u := by
      rintro _ ⟨t, -, rfl⟩ u
      exact hZX t t.2 u
    have hYC : ∀ y ∈ Y, y ∈ CHbar S a := by
      intro y hy
      obtain ⟨t, ht, rfl⟩ := hy
      refine mem_CHbar_of_odd_orderOf S h.mem_Q hYfix hYZ ⟨t, ht, rfl⟩ ?_
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT3) ⟨t, ht⟩
      have h1 : orderOf ((Xsub S a).subtype t) = orderOf t :=
        orderOf_injective _ (Xsub S a).subtype_injective t
      have h2 : orderOf t = 3 ^ k := by rw [← hk]; exact (Subgroup.orderOf_mk t ht).symm
      rw [h1, h2]
      exact Odd.pow (by decide)
    have hYN : ∀ y ∈ Y, ∀ l ∈ Lbar S a, y * l * y⁻¹ ∈ Lbar S a := by
      intro y hy l hl
      have hN := CH_le_normalizer_Lbar S a (hYC y hy)
      exact (Subgroup.mem_normalizer_iff.mp hN l).mp hl
    have hL2 : ∀ e ∈ Lbar S a, e * e = 1 := fun e he => by
      rw [← pow_two]
      exact sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj he
    have hLc : ∀ e ∈ Lbar S a, ∀ f ∈ Lbar S a, e * f = f * e := by
      intro e he f hf
      have h1 : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hL2 e he)
      have h2 : f⁻¹ = f := inv_eq_of_mul_eq_one_right (hL2 f hf)
      have h3 : (e * f)⁻¹ = e * f :=
        inv_eq_of_mul_eq_one_right (hL2 _ ((Lbar S a).mul_mem he hf))
      calc e * f = (e * f)⁻¹ := h3.symm
        _ = f⁻¹ * e⁻¹ := mul_inv_rev e f
        _ = f * e := by rw [h1, h2]
    have hOut' : ∀ E : Subgroup (Outer ↥(Xsub S a)), (∀ e ∈ E, e * e = 1) →
        Nat.card ↥E ≤ 2 ^ 0 := by
      intro E _
      have hle : Nat.card ↥E ≤ Nat.card (Outer ↥(Xsub S a)) := Subgroup.card_le_card_group E
      rw [hOut] at hle
      simpa using hle
    obtain ⟨A, hA2, hAc, hrA, hAr, hAT, hAcard⟩ :=
      CFSG.GroupTheory.exists_subgroup_card_le_of_normalizer (Xsub S a) hZX0 hOut'
        (Lbar S a) hLc hL2 (r := (r : Hbar z)) r.2 (Rbar_le_Lbar S a hαR) Y
        (by rintro _ ⟨t, -, rfl⟩; exact t.2) hYN
    have hA8 : Nat.card ↥A ≤ 8 := by
      refine hbound r hrD P A hA2 hAc hrA (fun x hx => Subtype.ext (hAr x hx)) ?_
      intro t ht x hx
      exact hAT (t : ↥(Xsub S a)) ⟨(t : ↥(Xsub S a)), ⟨t, ht, rfl⟩, rfl⟩ x hx
    have hLb8 : Nat.card ↥(Lbar S a) ≤
        8 * Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) := by
      calc Nat.card ↥(Lbar S a) ≤ Nat.card ↥A * 2 ^ 0 *
            Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) := hAcard
        _ ≤ 8 * Nat.card ↥(Lbar S a ⊓ Subgroup.centralizer (Xsub S a : Set (Hbar z))) := by
          rw [pow_zero, mul_one]
          exact Nat.mul_le_mul_right _ hA8
    exact false_of_card_Lbar_le_eight_mul_of_seven_dvd S h h217 hw4 hZ h7 hLb8

end CFSG.RankThree.GF2n.Stroth78

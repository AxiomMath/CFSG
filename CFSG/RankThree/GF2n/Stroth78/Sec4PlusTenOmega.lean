module

public import CFSG.RankThree.GF2n.Stroth78.Sec1One

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusFixedSq
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusZQFour
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusPerfect
import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeLift
import CFSG.RankThree.GF2n.Stroth78.Sec2Six
import CFSG.LargeExtraspecial.A2ModNaturalOmegaFix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem exists_alpha_of_card_ZQ_eq_four (S : Setting z E F) {a : G} {w : ℕ}
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
    ∃ α : ↥(Xsub S a), α ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) ∧
      aVec S h.mem_Q ∈ commSpace (rhoX S a α) ∧
      (¬ ∀ x : ↥(Xsub S a), rhoX S a x (aVec S h.mem_Q) = aVec S h.mem_Q) ∧
      ∀ y : ↥(Xsub S a), Odd (orderOf y) → rhoX S a y (aVec S h.mem_Q) = aVec S h.mem_Q →
        y * α = α * y := by
  have hD := rootClass_Xsub S h h217 h34
  have hZX := rhoZ_eq_self_of_mem_Xsub_of_card_ZQ_eq_four S h h217 h34 hZ
  have hR2 := card_Rbar_eq_two_of_card_ZQ_eq_four S h hZ
  obtain ⟨⟨α, hαR⟩, hα1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα1 : α ≠ 1 := fun h1 => hα1' (Subtype.ext h1)
  refine ⟨⟨α, h.Rbar_le_Xsub hαR⟩, Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hαR hα1),
    (mem_A2set_and_aVec_mem_of_mem_Rbar h hαR hα1).2, ?_, ?_⟩
  · intro hfix
    have hle := le_CHbar_of_perfect S h.mem_Q (commutator_Xsub_eq_of_threeFourPlus S h h217 h34)
      (fun y hy => hfix ⟨y, hy⟩) hZX
    have hcen : (⟨α, h.Rbar_le_Xsub hαR⟩ : ↥(Xsub S a)) ∈ Subgroup.center ↥(Xsub S a) :=
      Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (commute_of_mem_CHbar_of_card_Rbar_eq_two S a hR2 hαR hα1 (hle g.2))
    rw [hD.2.2.1, Subgroup.mem_bot] at hcen
    exact hα1 (congrArg Subtype.val hcen)
  · intro y hy hfix
    have hYX : Subgroup.closure {(y : Hbar z)} ≤ Xsub S a :=
      (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr y.2)
    have hYfix : ∀ t ∈ Subgroup.closure {(y : Hbar z)},
        rhoLin S t (aVec S h.mem_Q) = aVec S h.mem_Q := by
      intro t ht
      induction ht using Subgroup.closure_induction with
      | mem t ht =>
        rw [Set.mem_singleton_iff.mp ht]
        exact hfix
      | one => rw [rhoLin, map_one]; rfl
      | mul t s _ _ ht hs => rw [rhoLin_mul, LinearEquiv.mul_apply, hs, ht]
      | inv t _ ht =>
        rw [rhoLin_inv]
        calc (rhoLin S t)⁻¹ (aVec S h.mem_Q) =
            (rhoLin S t)⁻¹ (rhoLin S t (aVec S h.mem_Q)) := by rw [ht]
          _ = aVec S h.mem_Q := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    have hyC := mem_CHbar_of_odd_orderOf S h.mem_Q hYfix (fun t ht => hZX t (hYX ht))
      (Subgroup.subset_closure rfl) (by rwa [Subgroup.orderOf_coe])
    exact Subtype.ext (commute_of_mem_CHbar_of_card_Rbar_eq_two S a hR2 hαR hα1 hyC)


theorem not_lieModel_pOmegaMinus_of_card_ZQ_eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hZ : Nat.card ↥(ZQ z) = 4) {m : ℕ} (hm : 4 ≤ m) :
    ¬ CFSG.Blueprint.LieModel ↥(Xsub S a) .POmegaMinus m 2 1 := by
  intro hX
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  obtain ⟨φ, π, -, hinj, hπ, hQ⟩ := exists_natural_pOmegaMinus S h h217 h34 hm hX
  obtain ⟨α, hαD, haL, hnfix, hcomm⟩ := exists_alpha_of_card_ZQ_eq_four S h h217 h34 hZ
  have ha0 : aVec S h.mem_Q ≠ 0 := fun h0 => hnfix fun x => by rw [h0, map_zero]
  refine CFSG.LargeExtraspecial.A2Mod.false_of_commute_of_natural_omega (a2Action_Xsub S a)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m (ZMod 2)
      (by decide)) ?_ (CFSG.LieType.Universal.Spin.coe_quadMinus m (ZMod 2) 1 1) φ π hinj hπ hQ
    hαD haL ha0 fun y hy3 hfix => hcomm y ?_ hfix
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy3) with h1 | h1 <;>
      rw [h1] <;> decide

theorem not_lieModel_pOmegaPlus_of_card_ZQ_eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hZ : Nat.card ↥(ZQ z) = 4) {m : ℕ} (hm : 5 ≤ m) :
    ¬ CFSG.Blueprint.LieModel ↥(Xsub S a) .POmegaPlus m 2 1 := by
  intro hX
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  obtain ⟨φ, π, -, hinj, hπ, hQ⟩ := exists_natural_pOmegaPlus S h h217 h34 hm hX
  obtain ⟨α, hαD, haL, hnfix, hcomm⟩ := exists_alpha_of_card_ZQ_eq_four S h h217 h34 hZ
  have ha0 : aVec S h.mem_Q ≠ 0 := fun h0 => hnfix fun x => by rw [h0, map_zero]
  refine CFSG.LargeExtraspecial.A2Mod.false_of_commute_of_natural_omega (a2Action_Xsub S a)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m (ZMod 2)) ?_
    (CFSG.LieType.Universal.Spin.coe_quadPlus m (ZMod 2)) φ π hinj hπ hQ hαD haL ha0
    fun y hy3 hfix => hcomm y ?_ hfix
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy3) with h1 | h1 <;>
      rw [h1] <;> decide

end CFSG.RankThree.GF2n.Stroth78

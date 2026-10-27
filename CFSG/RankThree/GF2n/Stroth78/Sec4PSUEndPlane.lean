module

public import CFSG.RankThree.GF2n.Stroth78.Sec3OddInvariant

import CFSG.GroupTheory.ThreeTranspositions.FormLinearAlgebra
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open Module

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

namespace Sec4PSUEnd

theorem aVec_add_rhoLin_add_rhoLin_eq_zero (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    {ρ : Hbar z} (hρ3 : ρ ^ 3 = 1) (hρ1 : ρ ≠ 1)
    (hLρ : Lbar S a ≤ Subgroup.normalizer (Subgroup.zpowers ρ : Set (Hbar z)))
    {α₀ : Hbar z} (hα₀R : α₀ ∈ Rbar S a) (hα₀1 : α₀ ≠ 1) (hρα : ρ * α₀ = α₀ * ρ) :
    aVec S h.mem_Q + rhoLin S ρ (aVec S h.mem_Q) + rhoLin S (ρ * ρ) (aVec S h.mem_Q) = 0 ∧
      ∀ v ∈ commSpace (rhoLin S α₀), v = 0 ∨ v = aVec S h.mem_Q ∨
        v = rhoLin S ρ (aVec S h.mem_Q) ∨ v = rhoLin S (ρ * ρ) (aVec S h.mem_Q) := by
  classical
  have hrho1 : rhoLin S 1 = 1 := by simp [rhoLin]
  have hR : Odd (Nat.card (Subgroup.zpowers ρ)) := by
    rw [Nat.card_zpowers, orderOf_eq_prime hρ3 hρ1]
    decide
  have hYbot := inf_commSpaceFixer_eq_bot S h h217 hR hLρ α₀ hα₀R hα₀1
  have hinj : ∀ y y' : Subgroup.zpowers ρ,
      rhoLin S (y : Hbar z) (aVec S h.mem_Q) = rhoLin S (y' : Hbar z) (aVec S h.mem_Q) →
        y = y' := fun y y' hval =>
    eq_of_apply_aVec_eq_of_inf_commSpaceFixer_eq_bot S h hR hLρ hα₀R hα₀1 hYbot hval
  obtain ⟨q, hq⟩ : ∃ q, q = rhoLin S ρ (aVec S h.mem_Q) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = rhoLin S (ρ * ρ) (aVec S h.mem_Q) := ⟨_, rfl⟩
  rw [← hq, ← hs]
  have hsq : s = rhoLin S ρ q := by
    rw [hs, hq, rhoLin_mul, LinearEquiv.mul_apply]
  have hp0 : aVec S h.mem_Q ≠ 0 := aV_ne_zero S h.mem_Q h.not_mem_ZQ
  have hq0 : q ≠ 0 := by
    rw [hq]
    exact fun h0 => hp0 ((LinearEquiv.map_eq_zero_iff _).mp h0)
  have hs0 : s ≠ 0 := by
    rw [hs]
    exact fun h0 => hp0 ((LinearEquiv.map_eq_zero_iff _).mp h0)
  have hpq : aVec S h.mem_Q ≠ q := by
    intro he
    have h1 : (⟨1, one_mem _⟩ : Subgroup.zpowers ρ) = ⟨ρ, Subgroup.mem_zpowers ρ⟩ :=
      hinj _ _ (by
        show rhoLin S 1 (aVec S h.mem_Q) = rhoLin S ρ (aVec S h.mem_Q)
        rw [hrho1, ← hq]
        exact he)
    exact hρ1 (congrArg Subtype.val h1).symm
  have hqs : q ≠ s := by
    intro he
    apply hpq
    have he' : rhoLin S ρ (aVec S h.mem_Q) = rhoLin S ρ q := by
      rw [← hq, ← hsq]
      exact he
    exact (rhoLin S ρ).injective he'
  have hps : aVec S h.mem_Q ≠ s := by
    intro he
    have h1 : (⟨1, one_mem _⟩ : Subgroup.zpowers ρ) =
        ⟨ρ * ρ, mul_mem (Subgroup.mem_zpowers ρ) (Subgroup.mem_zpowers ρ)⟩ :=
      hinj _ _ (by
        show rhoLin S 1 (aVec S h.mem_Q) = rhoLin S (ρ * ρ) (aVec S h.mem_Q)
        rw [hrho1, ← hs]
        exact he)
    have h11 : (1 : Hbar z) = ρ * ρ := congrArg Subtype.val h1
    apply hρ1
    calc ρ = ρ * ρ * ρ := by rw [← h11, one_mul]
      _ = ρ ^ 3 := (pow_three' ρ).symm
      _ = 1 := hρ3
  have hpW : aVec S h.mem_Q ∈ commSpace (rhoLin S α₀) :=
    aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
      h.centerIn_Qa_not_le_Q hα₀R hα₀1
  have hqW : q ∈ commSpace (rhoLin S α₀) := by
    rw [hq]
    exact rhoLin_mem_commSpace_of_commute S hρα hpW
  have hsW : s ∈ commSpace (rhoLin S α₀) := by
    rw [hsq]
    exact rhoLin_mem_commSpace_of_commute S hρα hqW
  have hW2 : finrank (ZMod 2) (commSpace (rhoLin S α₀)) = 2 := by
    simpa [rhoLin] using
      (isTypeA_rhoBar_of_isA2Hbar S
        (isA2Hbar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
          h.centerIn_Qa_not_le_Q α₀ hα₀R hα₀1)).2.2.2.1
  have hsum : aVec S h.mem_Q + q + s = 0 := by
    by_contra hne
    have hli := linearIndependent_triple_zmod_two
      (x := (⟨aVec S h.mem_Q, hpW⟩ : commSpace (rhoLin S α₀)))
      (y := (⟨q, hqW⟩ : commSpace (rhoLin S α₀))) (z := (⟨s, hsW⟩ : commSpace (rhoLin S α₀)))
      (fun h0 => hp0 (congrArg Subtype.val h0)) (fun h0 => hq0 (congrArg Subtype.val h0))
      (fun h0 => hs0 (congrArg Subtype.val h0)) (fun h0 => hpq (congrArg Subtype.val h0))
      (fun h0 => hps (congrArg Subtype.val h0)) (fun h0 => hqs (congrArg Subtype.val h0))
      (fun h0 => hne (congrArg Subtype.val h0))
    have hle := hli.fintype_card_le_finrank
    rw [hW2, Fintype.card_fin] at hle
    omega
  refine ⟨hsum, fun v hv => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hv0, hvp, hvq, hvs⟩ := hne
  have hli := linearIndependent_triple_zmod_two
    (x := (⟨aVec S h.mem_Q, hpW⟩ : commSpace (rhoLin S α₀)))
    (y := (⟨q, hqW⟩ : commSpace (rhoLin S α₀))) (z := (⟨v, hv⟩ : commSpace (rhoLin S α₀)))
    (fun h0 => hp0 (congrArg Subtype.val h0)) (fun h0 => hq0 (congrArg Subtype.val h0))
    (fun h0 => hv0 (congrArg Subtype.val h0)) (fun h0 => hpq (congrArg Subtype.val h0))
    (fun h0 => hvp (congrArg Subtype.val h0).symm)
    (fun h0 => hvq (congrArg Subtype.val h0).symm)
    (fun h0 => hvs (by
      have h1 : aVec S h.mem_Q + q + v = 0 := congrArg Subtype.val h0
      exact add_left_cancel (h1.trans hsum.symm)))
  have hle := hli.fintype_card_le_finrank
  rw [hW2, Fintype.card_fin] at hle
  omega

end Sec4PSUEnd

end CFSG.RankThree.GF2n.Stroth78

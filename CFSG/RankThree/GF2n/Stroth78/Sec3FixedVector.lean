module

public import CFSG.RankThree.GF2n.Stroth78.Sec3LbarBound

import CFSG.LargeExtraspecial.DW4Burn

import CFSG.LargeExtraspecial.AS35ZSDefs
import CFSG.LargeExtraspecial.OrthoF2Eichler
import CFSG.LinearAlgebra.F2PlaneMaps
import CFSG.RankThree.GF2n.Stroth78.Sec2Seventeen
import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem aVec_not_mem_iSup_commSpace_of_odd (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {Y : Subgroup (Hbar z)} (hY : Odd (Nat.card Y))
    (hfix : ∀ y ∈ Y, rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q) :
    aVec S h.mem_Q ∉ ⨆ y ∈ Y, commSpace (rhoLin S y) := by
  let Q : Subgroup (Additive (QbarOf S) ≃ₗ[ZMod 2] Additive (QbarOf S)) :=
    Y.map (rhoGL S)
  have hQodd : Odd (Nat.card Q) := by
    have hcard : Nat.card Q = Nat.card Y := by
      simpa [Q] using Subgroup.card_map_of_injective (f := rhoGL S) (rhoGL_injective S)
    rw [hcard]
    exact hY
  have hfixQ : aVec S h.mem_Q ∈ CFSG.SignalizerFunctorTheorem.Quadratic.fixSub Q := by
    rw [CFSG.SignalizerFunctorTheorem.Quadratic.mem_fixSub]
    intro q hq
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
    simpa [rhoGL] using hfix y hy
  have hcopQ : Nat.Coprime 2 (Nat.card Q) := Nat.coprime_two_left.mpr hQodd
  have hcompl := CFSG.SignalizerFunctorTheorem.Quadratic.isCompl_fixSub_commSub
    (p := 2) hcopQ
  have hsup_le : (⨆ y ∈ Y, commSpace (rhoLin S y)) ≤
      CFSG.SignalizerFunctorTheorem.Quadratic.commSub Q := by
    refine iSup_le fun y => iSup_le fun hy => ?_
    intro v hv
    obtain ⟨u, rfl⟩ := CFSG.LargeExtraspecial.DW.W4.mem_commSpace.mp hv
    refine Submodule.subset_span ⟨rhoGL S y, Subgroup.mem_map_of_mem (rhoGL S) hy, u, ?_⟩
    simp [rhoGL]
  intro hmem
  have hcomm : aVec S h.mem_Q ∈ CFSG.SignalizerFunctorTheorem.Quadratic.commSub Q :=
    hsup_le hmem
  have hzero : aVec S h.mem_Q = 0 :=
    Submodule.disjoint_def.mp hcompl.disjoint (aVec S h.mem_Q) hfixQ hcomm
  exact aV_ne_zero S h.mem_Q h.not_mem_ZQ hzero

theorem rhoLin_apply_eq_self_of_odd_of_commute (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {y r : Hbar z} (hr : r ∈ Rbar S a) (hyr : y * r = r * y)
    (hy : Odd (orderOf y)) (hya : rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q) :
    ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v := by
  intro v hv
  by_cases hr1 : r = 1
  · rw [hr1] at hv
    have hbot : commSpace (rhoLin S (1 : Hbar z)) = ⊥ := by
      rw [show rhoLin S (1 : Hbar z) = 1 from by simp [rhoLin]]
      exact CFSG.LargeExtraspecial.OrthoF2.commSpace_one
    rw [hbot, Submodule.mem_bot] at hv
    rw [hv]
    simp
  · have hA2 : IsA2Hbar S r :=
      isA2Hbar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
        h.centerIn_Qa_not_le_Q r hr hr1
    have htype := isTypeA_rhoBar_of_isA2Hbar S hA2
    have hW : finrank (ZMod 2) (commSpace (rhoLin S r)) = 2 := by
      simpa [rhoLin] using htype.2.2.2.1
    have hcommρ : rhoLin S y * rhoLin S r = rhoLin S r * rhoLin S y := by
      have := congrArg (rhoLin S) hyr
      simpa [rhoLin_mul] using this
    have hyW : ∀ u ∈ commSpace (rhoLin S r), rhoLin S y u ∈ commSpace (rhoLin S r) :=
      fun u hu => CFSG.LargeExtraspecial.AS35ZS.apply_mem_commSpace_of_commute hcommρ hu
    have hoddy : Odd (orderOf (rhoLin S y)) := by
      rwa [orderOf_rhoLin]
    have ha : aVec S h.mem_Q ∈ commSpace (rhoLin S r) :=
      aV_mem_commSpace_rhoBar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa
        h.centerIn_Qa_not_le_Q hr hr1
    exact CFSG.LinearAlgebra.apply_eq_self_of_odd_of_apply_eq
      (W := commSpace (rhoLin S r)) hW hyW hoddy ha
      (aV_ne_zero S h.mem_Q h.not_mem_ZQ) hya v hv

end CFSG.RankThree.GF2n.Stroth78

module

public import CFSG.Sporadic.SmallOddCore.HSWordBound

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint

theorem hs_outer_card_le :
    Nat.card (Outer hsP) ≤ 2 := by
  have hAut := hs_card_mulAut_le
  have h2 : (88704000 : ℕ) = 2 * Nat.card hsP := by rw [card_hsP]
  obtain ⟨-, -, -, -, -, -, -, -, -, _, -, -, -, hconjinj⟩ :=
    hs_normalizing_model
  have hInn : Nat.card (inner hsP) = Nat.card hsP :=
    (Nat.card_congr (MonoidHom.ofInjective hconjinj).toEquiv).symm
  have hcard := (inner hsP).card_eq_card_quotient_mul_card_subgroup
  rw [hInn] at hcard
  have hpos : 0 < Nat.card hsP := Nat.card_pos
  have hle : Nat.card (Outer hsP) * Nat.card hsP ≤ 2 * Nat.card hsP := by
    rw [← h2]
    exact hcard ▸ hAut
  exact Nat.le_of_mul_le_mul_right hle hpos

theorem hs_full_automorphism_model :
    ∃ e : hsR ≃* MulAut hsP,
      (∀ (x : hsR) (p : hsP),
        ((e x p : hsP) : Equiv.Perm (Fin 3850)) = (x : Equiv.Perm (Fin 3850)) * p * (x : _)⁻¹) ∧
      (hsP.subgroupOf hsR).map e.toMonoidHom = inner hsP ∧
      Nonempty (Outer hsP ≃* Multiplicative (ZMod 2)) ∧ Nat.card (MulAut hsP) = 88704000 := by
  obtain ⟨hU2, -, hUP, hmap, hC, -⟩ := hs_normalizing_model
  have hUn : ∀ p ∈ hsP, hsU * p * hsU⁻¹ ∈ hsP := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  obtain ⟨e, he, himage, hout, hcard⟩ := full_automorphism_model hU2 hUP hUn hC hs_outer_card_le
  exact ⟨e, he, himage, hout, by rw [hcard, card_hsP]⟩

theorem hs_autModel :
    AutModel hsP hsR := by
  obtain ⟨hU2, -, hUP, hmap, hC, hRmem, -⟩ := hs_normalizing_model
  have hUn : ∀ p ∈ hsP, hsU * p * hsU⁻¹ ∈ hsP := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  obtain ⟨e, he, -⟩ := hs_full_automorphism_model
  refine autModel_of le_sup_left (fun x hx p hp => ?_) e he hC
  rcases (hRmem x).1 hx with hxP | hxU
  · exact hsP.mul_mem (hsP.mul_mem hxP hp) (hsP.inv_mem hxP)
  · have hUU : hsU * hsU = 1 := by rw [← sq, hU2]
    have hUinv : hsU⁻¹ = hsU := inv_eq_of_mul_eq_one_right hUU
    have h1 : hsU⁻¹ * p * hsU ∈ hsP := by
      have := hUn p hp
      rw [hUinv] at this ⊢
      exact this
    have : x * p * x⁻¹ = (x * hsU) * (hsU⁻¹ * p * hsU) * (x * hsU)⁻¹ := by group
    rw [this]
    exact hsP.mul_mem (hsP.mul_mem hxU h1) (hsP.inv_mem hxU)

theorem hs_almost_simple_odd_core
    {X : Type*} [Group X]
    [Finite X] (S : Subgroup X) [S.Normal] (hS : Nonempty (S ≃* NativeSporadic.HS))
    (hC : centralizer (S : Set X) = ⊥) (t : X) (ht : orderOf t = 2) :
    CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥ := by
  obtain ⟨ψ⟩ := hS
  obtain ⟨-, -, -, -, -, -, -, hodd⟩ :=
    hs_involution_centralizers
  have hidx : Nat.card hsR ≤ 2 * Nat.card hsP := by
    rw [hs_normalizing_model.2.2.2.2.2.2.2.2.1, card_hsP]
  exact oddCore_centralizer_eq_bot hs_autModel hidx hodd S (ψ.trans hsPermEquiv) hC t ht

theorem hs_not_comm :
    ∃ a b : NativeSporadic.HS, a * b ≠ b * a := by
  obtain ⟨-, -, -, hc, -⟩ := AT_HS_image_pair_count
  refine ⟨hsPermEquiv.symm hsa0, hsPermEquiv.symm hsa1, fun h => ?_⟩
  have h' := congrArg (fun x => ((hsPermEquiv x : hsP) : Equiv.Perm (Fin 3850))) h
  simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h'
  exact mul_ne_mul_of_orderOf_commutator hc (by norm_num) h'

end CFSG.Sporadic.SmallOddCore

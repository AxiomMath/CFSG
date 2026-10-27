module

public import CFSG.Sporadic.SmallOddCore.McLWordBound

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint

theorem mcl_outer_card_le :
    Nat.card (Outer mclP) ≤ 2 := by
  have hAut := mcl_card_mulAut_le
  have h2 : (1796256000 : ℕ) = 2 * Nat.card mclP := by rw [card_mclP]
  obtain ⟨-, -, -, -, -, -, -, -, -, _, -, -, -, hconjinj⟩ :=
    mcl_normalizing_model
  have hInn : Nat.card (inner mclP) = Nat.card mclP :=
    (Nat.card_congr (MonoidHom.ofInjective hconjinj).toEquiv).symm
  have hcard := (inner mclP).card_eq_card_quotient_mul_card_subgroup
  rw [hInn] at hcard
  have hpos : 0 < Nat.card mclP := Nat.card_pos
  have hle : Nat.card (Outer mclP) * Nat.card mclP ≤ 2 * Nat.card mclP := by
    rw [← h2]
    exact hcard ▸ hAut
  exact Nat.le_of_mul_le_mul_right hle hpos

theorem mcl_full_automorphism_model :
    ∃ e : mclR ≃* MulAut mclP,
      (∀ (x : mclR) (p : mclP),
        ((e x p : mclP) : Equiv.Perm (Fin 275)) = (x : Equiv.Perm (Fin 275)) * p * (x : _)⁻¹) ∧
      (mclP.subgroupOf mclR).map e.toMonoidHom = inner mclP ∧
      Nonempty (Outer mclP ≃* Multiplicative (ZMod 2)) ∧ Nat.card (MulAut mclP) = 1796256000 := by
  obtain ⟨hU2, -, hUP, hmap, hC, -⟩ := mcl_normalizing_model
  have hUn : ∀ p ∈ mclP, mclU * p * mclU⁻¹ ∈ mclP := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  obtain ⟨e, he, himage, hout, hcard⟩ := full_automorphism_model hU2 hUP hUn hC mcl_outer_card_le
  exact ⟨e, he, himage, hout, by rw [hcard, card_mclP]⟩

theorem mcl_autModel :
    AutModel mclP mclR := by
  obtain ⟨hU2, -, hUP, hmap, hC, hRmem, -⟩ := mcl_normalizing_model
  have hUn : ∀ p ∈ mclP, mclU * p * mclU⁻¹ ∈ mclP := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  obtain ⟨e, he, -⟩ := mcl_full_automorphism_model
  refine autModel_of le_sup_left (fun x hx p hp => ?_) e he hC
  rcases (hRmem x).1 hx with hxP | hxU
  · exact mclP.mul_mem (mclP.mul_mem hxP hp) (mclP.inv_mem hxP)
  · have hUU : mclU * mclU = 1 := by rw [← sq, hU2]
    have hUinv : mclU⁻¹ = mclU := inv_eq_of_mul_eq_one_right hUU
    have h1 : mclU⁻¹ * p * mclU ∈ mclP := by
      have := hUn p hp
      rw [hUinv] at this ⊢
      exact this
    have : x * p * x⁻¹ = (x * mclU) * (mclU⁻¹ * p * mclU) * (x * mclU)⁻¹ := by group
    rw [this]
    exact mclP.mul_mem (mclP.mul_mem hxU h1) (mclP.inv_mem hxU)

theorem mcl_almost_simple_odd_core
    {X : Type*} [Group X]
    [Finite X] (S : Subgroup X) [S.Normal] (hS : Nonempty (S ≃* NativeSporadic.McL))
    (hC : centralizer (S : Set X) = ⊥) (t : X) (ht : orderOf t = 2) :
    CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥ := by
  obtain ⟨ψ⟩ := hS
  obtain ⟨-, -, -, -, -, -, -, hodd⟩ :=
    mcl_involution_centralizers
  have hidx : Nat.card mclR ≤ 2 * Nat.card mclP := by
    rw [mcl_normalizing_model.2.2.2.2.2.2.2.2.1, card_mclP]
  exact oddCore_centralizer_eq_bot mcl_autModel hidx hodd S (ψ.trans mclPermEquiv) hC t ht

theorem mcl_not_comm :
    ∃ a b : NativeSporadic.McL, a * b ≠ b * a := by
  obtain ⟨-, -, -, hc, -⟩ := AT_McL_image_pair_count
  refine ⟨mclPermEquiv.symm mcla0, mclPermEquiv.symm mcla1, fun h => ?_⟩
  have h' := congrArg (fun x => ((mclPermEquiv x : mclP) : Equiv.Perm (Fin 275))) h
  simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h'
  exact mul_ne_mul_of_orderOf_commutator hc (by norm_num) h'

end CFSG.Sporadic.SmallOddCore

module

public import CFSG.Sporadic.SmallOddCore.J3WordBound

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint

theorem j3_outer_card_le :
    Nat.card (Outer j3P) ≤ 2 := by
  obtain ⟨-, -, hAut, h2⟩ := ctuc_j3_generator_image_word_bound
  obtain ⟨-, -, -, -, -, -, -, -, -, _, -, -, -, hconjinj⟩ :=
    ctuc_j3_normalizing_involution_permutation_model
  have hInn : Nat.card (inner j3P) = Nat.card j3P :=
    (Nat.card_congr (MonoidHom.ofInjective hconjinj).toEquiv).symm
  have hcard := (inner j3P).card_eq_card_quotient_mul_card_subgroup
  rw [hInn] at hcard
  have hpos : 0 < Nat.card j3P := Nat.card_pos
  have hle : Nat.card (Outer j3P) * Nat.card j3P ≤ 2 * Nat.card j3P := by
    rw [← h2]
    exact hcard ▸ hAut
  exact Nat.le_of_mul_le_mul_right hle hpos

theorem ctuc_j3_full_automorphism_permutation_model :
    ∃ e : j3R ≃* MulAut j3P,
      (∀ (x : j3R) (p : j3P),
        ((e x p : j3P) : Equiv.Perm (Fin 6156)) = (x : Equiv.Perm (Fin 6156)) * p * (x : _)⁻¹) ∧
      (j3P.subgroupOf j3R).map e.toMonoidHom = inner j3P ∧
      Nonempty (Outer j3P ≃* Multiplicative (ZMod 2)) ∧ Nat.card (MulAut j3P) = 100465920 := by
  obtain ⟨hU2, -, hUP, hmap, hC, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  have hUn : ∀ p ∈ j3P, j3u * p * j3u⁻¹ ∈ j3P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  obtain ⟨e, he, himage, hout, hcard⟩ := full_automorphism_model hU2 hUP hUn hC j3_outer_card_le
  exact ⟨e, he, himage, hout, by rw [hcard, card_j3P]⟩

theorem j3_autModel :
    AutModel j3P j3R := by
  obtain ⟨hU2, -, hUP, hmap, hC, hRmem, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  have hUn : ∀ p ∈ j3P, j3u * p * j3u⁻¹ ∈ j3P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  obtain ⟨e, he, -⟩ := ctuc_j3_full_automorphism_permutation_model
  refine autModel_of le_sup_left (fun x hx p hp => ?_) e he hC
  rcases (hRmem x).1 hx with hxP | hxU
  · exact j3P.mul_mem (j3P.mul_mem hxP hp) (j3P.inv_mem hxP)
  · have hUU : j3u * j3u = 1 := by rw [← sq, hU2]
    have hUinv : j3u⁻¹ = j3u := inv_eq_of_mul_eq_one_right hUU
    have h1 : j3u⁻¹ * p * j3u ∈ j3P := by
      have := hUn p hp
      rw [hUinv] at this ⊢
      exact this
    have : x * p * x⁻¹ = (x * j3u) * (j3u⁻¹ * p * j3u) * (x * j3u)⁻¹ := by group
    rw [this]
    exact j3P.mul_mem (j3P.mul_mem hxU h1) (j3P.inv_mem hxU)

theorem ctuc_j3_almost_simple_involution_centralizer_odd_core_trivial
    {X : Type*} [Group X]
    [Finite X] (S : Subgroup X) [S.Normal] (hS : Nonempty (S ≃* NativeSporadic.J3))
    (hC : centralizer (S : Set X) = ⊥) (t : X) (ht : orderOf t = 2) :
    CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥ := by
  obtain ⟨ψ⟩ := hS
  obtain ⟨-, -, -, -, -, -, -, hodd⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  have hidx : Nat.card j3R ≤ 2 * Nat.card j3P := by
    rw [ctuc_j3_normalizing_involution_permutation_model.2.2.2.2.2.2.2.2.1, card_j3P]
  exact oddCore_centralizer_eq_bot j3_autModel hidx hodd S (ψ.trans j3PermEquiv) hC t ht

theorem j3_not_comm :
    ∃ a b : NativeSporadic.J3, a * b ≠ b * a := by
  obtain ⟨-, -, -, hc, -⟩ := AT_J3_image_pair_count
  refine ⟨j3PermEquiv.symm j3a, j3PermEquiv.symm j3b, fun h => ?_⟩
  have h' := congrArg (fun x => ((j3PermEquiv x : j3P) : Equiv.Perm (Fin 6156))) h
  simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h'
  exact mul_ne_mul_of_orderOf_commutator hc (by norm_num) h'

theorem ctuc_j3_generalized_fitting_involution_centralizer_odd_core_trivial
    {X : Type*}
    [Group X] [Finite X] (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hJ : Nonempty (CFSG.generalizedFitting X ≃* NativeSporadic.J3)) (t : X)
    (ht : orderOf t = 2) : CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥ := by
  have : (CFSG.generalizedFitting X).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  obtain ⟨ψ⟩ := hJ
  have hnab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := j3_not_comm
    refine ⟨ψ.symm a, ψ.symm b, fun h => hab ?_⟩
    have := congrArg ψ h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  exact ctuc_j3_almost_simple_involution_centralizer_odd_core_trivial _ ⟨ψ⟩
    (centralizer_generalizedFitting_eq_bot hF hnab) t ht

end CFSG.Sporadic.SmallOddCore

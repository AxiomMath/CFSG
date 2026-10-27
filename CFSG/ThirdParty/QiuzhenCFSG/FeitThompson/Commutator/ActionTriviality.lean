module

import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Sylow

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas

namespace CFSG
end CFSG
open CFSG

/-- If all action commutators are trivial, then the action is trivial. -/
public theorem CFSG.actsTrivially_of_commutatorAction_eq_bot
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (hcomm_bot : commutatorAction (A := A) (G := G) = ⊥) :
    ActsTrivially (A := A) (G := G) := by
  simp [ActsTrivially]
  intro a g
  have hgen_mem : g⁻¹ * (a • g) ∈ commutatorAction (A := A) (G := G) := by
    rw [commutatorAction_eq_closure (G := G) (A := A)]
    exact Subgroup.subset_closure ⟨a, g, rfl⟩
  have hgen_eq_one : g⁻¹ * (a • g) = 1 := by
    have : g⁻¹ * (a • g) ∈ (⊥ : Subgroup G) := by
      simpa [hcomm_bot] using hgen_mem
    simpa using this
  have hmul := congrArg (fun x : G => g * x) hgen_eq_one
  simpa [mul_assoc] using hmul

/-- If `⁅⁅G, A⁆, A⁆ = ⊥` and `⁅⁅G, A⁆, A⁆ = ⁅G, A⁆`, then the action is trivial. -/
public theorem CFSG.actsTrivially_of_commutatorAction₂_eq_bot_of_eq
    {G A : Type*} [Group G] [Group A] [MulDistribMulAction A G]
    (hcomm_eq : commutatorAction₂ (A := A) (G := G) = commutatorAction (A := A) (G := G))
    (hcomm₂_bot : commutatorAction₂ (A := A) (G := G) = ⊥) :
    ActsTrivially (A := A) (G := G) := by
  apply actsTrivially_of_commutatorAction_eq_bot (G := G) (A := A)
  calc
    commutatorAction (A := A) (G := G) = commutatorAction₂ (A := A) (G := G) := by
      simpa using hcomm_eq.symm
    _ = ⊥ := hcomm₂_bot

/-- In a finite group, if `C_G(A)` complements `⁅G, A⁆` and contains all prime-order elements,
then the action is trivial. -/
public theorem CFSG.actsTrivially_of_prime_order_mem_fixedPointSubgroup_of_isCompl
    {G A : Type*} [Group G] [Finite G] [Group A] [MulDistribMulAction A G]
    (hcompl : IsCompl (fixedPointSubgroup A G) (commutatorAction (A := A) (G := G)))
    (hfix : ∀ g : G, Nat.Prime (orderOf g) → g ∈ fixedPointSubgroup A G) :
    ActsTrivially (A := A) (G := G) := by
  let C : Subgroup G := commutatorAction (A := A) (G := G)
  have hC_bot : C = ⊥ := by
    by_contra hC_ne_bot
    have hcard_ne_one : Nat.card C ≠ 1 := by
      intro hcard_one
      exact hC_ne_bot ((Subgroup.card_eq_one (H := C)).1 hcard_one)
    rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨p, hp_prime, hp_dvd⟩
    letI : Fact p.Prime := ⟨hp_prime⟩
    letI : Fintype C := Fintype.ofFinite C
    have hp_dvd' : p ∣ Fintype.card C := by
      simpa [Nat.card_eq_fintype_card] using hp_dvd
    obtain ⟨x, hx_order⟩ := _root_.exists_prime_orderOf_dvd_card (G := C) p hp_dvd'
    have hx_order_G : orderOf ((x : C) : G) = p := by
      simpa [Subgroup.orderOf_coe] using hx_order
    have hx_fixed : ((x : C) : G) ∈ fixedPointSubgroup A G := by
      apply hfix
      simpa [hx_order_G] using hp_prime
    have hx_comm : ((x : C) : G) ∈ C := x.property
    have hinf_bot : (fixedPointSubgroup A G ⊓ C) = ⊥ := by
      simpa [C] using hcompl.inf_eq_bot
    have hx_bot_mem : ((x : C) : G) ∈ (⊥ : Subgroup G) := by
      have hx_inf : ((x : C) : G) ∈ (fixedPointSubgroup A G) ⊓ C := ⟨hx_fixed, hx_comm⟩
      simpa [hinf_bot] using hx_inf
    have hx_eq_one_G : ((x : C) : G) = 1 := by simpa using hx_bot_mem
    have hx_eq_one_C : x = 1 := Subtype.ext hx_eq_one_G
    have h1p : 1 = p := by simpa [hx_eq_one_C] using hx_order
    exact hp_prime.ne_one h1p.symm
  simpa [C, hC_bot] using
    (actsTrivially_of_commutatorAction_eq_bot (G := G) (A := A) (hcomm_bot := by simpa [C] using hC_bot))

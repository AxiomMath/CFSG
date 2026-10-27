module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.ActionTriviality
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.CoprimeAction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.MinimalNormal
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
Small infrastructure for `piCore` used in Proposition-style coprime Hall lemmas.

`piCore π G` is defined in `BGsection1/Defs.lean` as the supremum of all normal `π`-subgroups of `G`.
The following helper is the one-line `le_sSup` wrapper used to inject a specific normal `π`-subgroup
into the `π`-core.
-/

public lemma CFSG.le_piCore_of_normal_isPiSubgroup {G : Type*} [Group G]
    (π : Set Nat.Primes) (K : Subgroup G) [K.Normal]
    (hKπ : IsPiSubgroup (G := G) π K) :
    K ≤ piCore π G := by
  -- `piCore` is the supremum of all normal `π`-subgroups.
  exact le_sSup (show K ∈ {K : Subgroup G | K.Normal ∧ IsPiSubgroup (G := G) π K} from ⟨‹_›, hKπ⟩)

public theorem CFSG.exists_mem_fixedPointSubgroup_eq_map_conj_of_isHallSubgroup_of_isInvariant
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (π : Set Nat.Primes) :
    ∀ H₁ H₂ : Subgroup G,
      IsHallSubgroup π H₁ →
        IsHallSubgroup π H₂ →
          IsInvariant A G H₁ →
            IsInvariant A G H₂ →
              ∃ g : G, g ∈ fixedPointSubgroup A G ∧ H₂ = H₁.map (MulAut.conj g) := by
  intro H₁ H₂ hHall₁ hHall₂ hInv₁ hInv₂
  simpa using
    exists_fixedPoint_conj_of_isHallSubgroup_of_isInvariant
      (G := G) (A := A) hsolv hcoprime π hHall₁ hHall₂ hInv₁ hInv₂

public theorem CFSG.fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (π : Set Nat.Primes) :
    ∀ (H : Subgroup G) [H.Normal] (hHinv : IsInvariant A G H),
      letI : MulDistribMulAction A (G ⧸ H) :=
        quotientMulDistribMulAction (A := A) (G := G) H hHinv
      fixedPointSubgroup A (G ⧸ H) = (fixedPointSubgroup A G).map (QuotientGroup.mk' H) := by
  let _ := π
  intro H _hHnorm hHinv
  simpa using
    fixedPointSubgroup_quotient_eq_map_of_solvable_coprime
      (G := G) (A := A) hsolv hcoprime H hHinv


public theorem CFSG.commutatorAction_le_piCore_of_hall_complement_le_fixedPointSubgroup
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (π : Set Nat.Primes) :
    ∀ Hπ' : Subgroup G,
      IsHallSubgroup {p | p ∉ π} Hπ' →
        Hπ' ≤ fixedPointSubgroup A G → commutatorAction (A := A) (G := G) ≤ piCore π G := by
  intro Hπ' hHallπ' hHπ'fix
  obtain ⟨Hπ, hHallπ, hHπinv⟩ :=
    exists_isHallSubgroup_isInvariant (G := G) (A := A) hsolv hcoprime π
  have hcop_cards : Nat.Coprime (Nat.card Hπ') (Nat.card Hπ) := by
    refine Nat.coprime_of_dvd ?_
    intro p hp_prime hp_dvd_Hπ' hp_dvd_Hπ
    have hp_not_mem : (⟨p, hp_prime⟩ : Nat.Primes) ∉ π :=
      hHallπ'.p_in_pi_of_p_dvd_card ⟨p, hp_prime⟩ hp_dvd_Hπ'
    have hp_mem : (⟨p, hp_prime⟩ : Nat.Primes) ∈ π :=
      hHallπ.p_in_pi_of_p_dvd_card ⟨p, hp_prime⟩ hp_dvd_Hπ
    exact (hp_not_mem hp_mem).elim
  have hcop_indices : Nat.Coprime Hπ.index Hπ'.index := by
    refine Nat.coprime_of_dvd ?_
    intro p hp_prime hp_dvd_Hπidx hp_dvd_Hπ'idx
    have hp_not_mem : (⟨p, hp_prime⟩ : Nat.Primes) ∉ π :=
      hHallπ.p_in_pi_of_p_dvd_index ⟨p, hp_prime⟩ hp_dvd_Hπidx
    have hp_mem : (⟨p, hp_prime⟩ : Nat.Primes) ∈ π := by
      have hnot_not_mem :=
        hHallπ'.p_in_pi_of_p_dvd_index ⟨p, hp_prime⟩ hp_dvd_Hπ'idx
      change ¬ ((⟨p, hp_prime⟩ : Nat.Primes) ∉ π) at hnot_not_mem
      exact Classical.not_not.mp hnot_not_mem
    exact (hp_not_mem hp_mem).elim
  have hcard_dvd_index : Nat.card Hπ' ∣ Hπ.index := by
    have hcard_dvd_G : Nat.card Hπ' ∣ Nat.card G := Subgroup.card_subgroup_dvd_card Hπ'
    have hcard_dvd_mul : Nat.card Hπ' ∣ Hπ.index * Nat.card Hπ := by
      simpa [Subgroup.index_mul_card] using hcard_dvd_G
    exact hcop_cards.dvd_of_dvd_mul_right hcard_dvd_mul
  have hindex_dvd_card : Hπ.index ∣ Nat.card Hπ' := by
    have hindex_dvd_G : Hπ.index ∣ Nat.card G := Subgroup.index_dvd_card (H := Hπ)
    have hindex_dvd_mul : Hπ.index ∣ Nat.card Hπ' * Hπ'.index := by
      simpa [Subgroup.card_mul_index] using hindex_dvd_G
    exact hcop_indices.dvd_of_dvd_mul_right hindex_dvd_mul
  have hcard_eq_index : Nat.card Hπ' = Hπ.index :=
    Nat.dvd_antisymm hcard_dvd_index hindex_dvd_card
  have hcard_mul : Nat.card Hπ' * Nat.card Hπ = Nat.card G := by
    calc
      Nat.card Hπ' * Nat.card Hπ = Hπ.index * Nat.card Hπ := by rw [hcard_eq_index]
      _ = Nat.card G := Subgroup.index_mul_card (H := Hπ)
  have hcomp : Subgroup.IsComplement' Hπ' Hπ :=
    Subgroup.isComplement'_of_coprime hcard_mul hcop_cards
  have hcomm_le_Hπ : commutatorAction (A := A) (G := G) ≤ Hπ := by
    rw [commutatorAction_eq_closure (G := G) (A := A)]
    refine (Subgroup.closure_le (K := Hπ)).2 ?_
    intro x hx
    rcases hx with ⟨a, g, rfl⟩
    rcases (hcomp.existsUnique g).exists with ⟨⟨⟨k, hk⟩, ⟨h, hh⟩⟩, rfl⟩
    have hkfix : a • k = k := hHπ'fix hk a
    have hah : a • h ∈ Hπ := (hHπinv.invariant a h).1 hh
    have hmem : h⁻¹ * (a • h) ∈ Hπ := Hπ.mul_mem (Hπ.inv_mem hh) hah
    simpa [smul_mul', hkfix, mul_assoc] using hmem
  have hcomm_pi : IsPiSubgroup (G := G) π (commutatorAction (A := A) (G := G)) := by
    intro p hp_dvd
    exact hHallπ.p_in_pi_of_p_dvd_card p
      (dvd_trans hp_dvd (Subgroup.card_dvd_of_le hcomm_le_Hπ))
  letI : (commutatorAction (A := A) (G := G)).Normal :=
    (commutatorAction_normal_and_invariant (A := A) (G := G)).1
  exact
    le_piCore_of_normal_isPiSubgroup (G := G) π (commutatorAction (A := A) (G := G)) hcomm_pi

public theorem CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    fixedPointSubgroup A G ⊔ commutatorAction (A := A) (G := G) = ⊤ := by
  simpa using
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_fixedPointQuotientImage
      (G := G) (A := A)
      (hfixed_quotient_image := fun (H : Subgroup G) (_ : H.Normal) (hHinv : IsInvariant A G H) =>
        fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
          (G := G) (A := A) hsolv hcoprime (π := (∅ : Set Nat.Primes)) H hHinv)

public theorem CFSG.commutatorAction₂_eq_commutatorAction_of_solvable_coprime
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    commutatorAction₂ (A := A) (G := G) = commutatorAction (A := A) (G := G) := by
  let _ := (inferInstance : Finite G)
  let _ := (inferInstance : Finite A)
  let _ := hsolv
  simpa using commutatorAction₂_eq_commutatorAction_of_coprime (G := G) (A := A) hcoprime

public theorem CFSG.actsTrivially_of_commutatorAction₂_eq_bot_of_solvable_coprime
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    commutatorAction₂ (A := A) (G := G) = ⊥ → ActsTrivially (A := A) (G := G) := by
  intro hcomm₂_bot
  exact
    actsTrivially_of_commutatorAction₂_eq_bot_of_eq (G := G) (A := A)
      (commutatorAction₂_eq_commutatorAction_of_solvable_coprime (G := G) (A := A) hsolv hcoprime)
      hcomm₂_bot

public theorem CFSG.isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    IsMulCommutative G → IsCompl (fixedPointSubgroup A G) (commutatorAction (A := A) (G := G)) := by
  intro hcomm
  have hsup :
      fixedPointSubgroup A G ⊔ commutatorAction (A := A) (G := G) = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime (G := G) (A := A) hsolv hcoprime
  exact
    isCompl_fixedPointSubgroup_commutatorAction_of_sup_eq_top_of_coprime_of_isMulCommutative
      (G := G) (A := A) hsup hcoprime hcomm

public theorem CFSG.actsTrivially_of_isMulCommutative_and_prime_order_mem_fixedPointSubgroup
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A] [MulDistribMulAction A G]
    (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    IsMulCommutative G →
      (∀ g : G, Nat.Prime (orderOf g) → g ∈ fixedPointSubgroup A G) → ActsTrivially (A := A) (G := G) := by
  intro hcomm hfix
  have hcompl :
      IsCompl (fixedPointSubgroup A G) (commutatorAction (A := A) (G := G)) := by
    simpa using
      (isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
        (G := G) (A := A) hsolv hcoprime hcomm)
  exact
    actsTrivially_of_prime_order_mem_fixedPointSubgroup_of_isCompl
      (G := G) (A := A) hcompl hfix

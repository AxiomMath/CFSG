module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

namespace CFSG
end CFSG
open CFSG

/-!
# Automorphisms of `A₄`

The conjugation map `S₄ → Aut(A₄)` is injective by the general
centralizer argument for alternating groups.  For surjectivity, choose a
3-cycle `x` and a double transposition `y` generating `A₄`.  An automorphism
is determined by its values on this pair.  There are eight elements of order
three and three elements of order two in `A₄`, so `|Aut(A₄)| ≤ 24`.
The conjugation injection supplies the reverse inequality.
-/

noncomputable section

namespace CFSG.GroupTheory.AutAlternating

open Equiv
open Equiv.Perm

private def a4xPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 0 2

private theorem a4xPerm_three : a4xPerm.IsThreeCycle := by
  exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private def a4x : alternatingGroup (Fin 4) :=
  ⟨a4xPerm, a4xPerm_three.mem_alternatingGroup⟩

private def a4yPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

private theorem a4yPerm_mem : a4yPerm ∈ alternatingGroup (Fin 4) := by
  change Equiv.Perm.sign a4yPerm = 1
  rw [a4yPerm, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1),
    Equiv.Perm.sign_swap (by decide : (2 : Fin 4) ≠ 3)]
  norm_num

private def a4y : alternatingGroup (Fin 4) := ⟨a4yPerm, a4yPerm_mem⟩

private theorem a4x_order : orderOf a4x = 3 := by
  rw [← Subgroup.orderOf_coe]
  exact a4xPerm_three.orderOf

private theorem a4y_order : orderOf a4y = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide
  · intro hy
    have hperm : a4yPerm ≠ 1 := by decide
    exact hperm (by simpa [a4y] using congrArg Subtype.val hy)

private theorem a4_order_three_iff_cycleType
    (g : alternatingGroup (Fin 4)) :
    orderOf g = 3 ↔ (g : Equiv.Perm (Fin 4)).cycleType = {3} := by
  rw [← Subgroup.orderOf_coe]
  constructor
  · intro hg
    have hp : Nat.Prime (orderOf (g : Equiv.Perm (Fin 4))) := by
      rw [hg]
      exact Nat.prime_three
    obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hp
    rw [hg] at hn
    have hsum' : (g : Equiv.Perm (Fin 4)).cycleType.sum ≤ 4 := by
      calc
        (g : Equiv.Perm (Fin 4)).cycleType.sum =
            (g : Equiv.Perm (Fin 4)).support.card :=
          Equiv.Perm.sum_cycleType (g : Equiv.Perm (Fin 4))
        _ ≤ Fintype.card (Fin 4) :=
          (g : Equiv.Perm (Fin 4)).support.card_le_univ
        _ = 4 := by simp
    have hsum : 3 * (n + 1) ≤ 4 := by
      rw [hn, Multiset.sum_replicate] at hsum'
      simpa [mul_comm] using hsum'
    have hn0 : n = 0 := by omega
    simpa [hn0] using hn
  · intro hg
    exact Equiv.Perm.IsThreeCycle.orderOf hg

private theorem a4_order_two_iff_cycleType
    (g : alternatingGroup (Fin 4)) :
    orderOf g = 2 ↔ (g : Equiv.Perm (Fin 4)).cycleType = {2, 2} := by
  rw [← Subgroup.orderOf_coe]
  constructor
  · intro hg
    have hcases := alternatingGroup.mem_kleinFour_of_order_two_pow
      (show Nat.card (Fin 4) = 4 by simp) g.property
      (show orderOf (g : Equiv.Perm (Fin 4)) ∣ 2 ^ 1 by simp [hg])
    rcases hcases with hzero | htwo
    · have hone : (g : Equiv.Perm (Fin 4)) = 1 :=
        Equiv.Perm.cycleType_eq_zero.mp hzero
      rw [hone, orderOf_one] at hg
      norm_num at hg
    · exact htwo
  · intro hg
    rw [← Equiv.Perm.lcm_cycleType, hg]
    norm_num

private theorem a4_card_order_three :
    (Finset.univ.filter fun g : alternatingGroup (Fin 4) =>
      orderOf g = 3).card = 8 := by
  have hset :
      (Finset.univ.filter fun g : alternatingGroup (Fin 4) => orderOf g = 3) =
        (Finset.univ.filter fun g : alternatingGroup (Fin 4) =>
          (g : Equiv.Perm (Fin 4)).cycleType = {3}) := by
    ext g
    simp [a4_order_three_iff_cycleType]
  rw [hset, AlternatingGroup.card_of_cycleType]
  norm_num [Nat.factorial, show Even 4 by decide]

private theorem a4_card_order_two :
    (Finset.univ.filter fun g : alternatingGroup (Fin 4) =>
      orderOf g = 2).card = 3 := by
  have hset :
      (Finset.univ.filter fun g : alternatingGroup (Fin 4) => orderOf g = 2) =
        (Finset.univ.filter fun g : alternatingGroup (Fin 4) =>
          (g : Equiv.Perm (Fin 4)).cycleType = {2, 2}) := by
    ext g
    simp [a4_order_two_iff_cycleType]
  rw [hset, AlternatingGroup.card_of_cycleType]
  norm_num [Nat.factorial, show Even 6 by decide]

private theorem a4y_cycleType : a4yPerm.cycleType = {2, 2} := by
  exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)

private theorem a4x_a4y_generate :
    Subgroup.closure ({a4x, a4y} : Set (alternatingGroup (Fin 4))) = ⊤ := by
  let K : Subgroup (alternatingGroup (Fin 4)) :=
    alternatingGroup.kleinFour (Fin 4)
  let H : Subgroup (alternatingGroup (Fin 4)) :=
    Subgroup.closure ({a4x, a4y} : Set _)
  have hxH : a4x ∈ H := Subgroup.subset_closure (by simp)
  have hyH : a4y ∈ H := Subgroup.subset_closure (by simp)
  have hyK : a4y ∈ K := by
    rw [← SetLike.mem_coe,
      alternatingGroup.coe_kleinFour_of_card_eq_four (by simp)]
    exact Or.inr a4y_cycleType
  let y' : alternatingGroup (Fin 4) := a4x * a4y * a4x⁻¹
  have hy'K : y' ∈ K := by
    have hKnormal : K.Normal := by
      dsimp [K]
      exact alternatingGroup.normal_kleinFour (by simp)
    exact hKnormal.conj_mem a4y hyK a4x
  have hy'H : y' ∈ H := H.mul_mem (H.mul_mem hxH hyH) (H.inv_mem hxH)
  have hy_ne : a4y ≠ 1 := by
    intro h
    have hperm : a4yPerm ≠ 1 := by decide
    exact hperm (by simpa [a4y] using congrArg Subtype.val h)
  have hy'_ne : y' ≠ 1 := by
    intro h
    have hperm : ((y' : alternatingGroup (Fin 4)) :
        Equiv.Perm (Fin 4)) ≠ 1 := by
      decide
    exact hperm (by simpa using congrArg Subtype.val h)
  have hyy' : a4y ≠ y' := by
    intro h
    have hperm : ((a4y : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)) ≠
        ((y' : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4)) := by
      decide
    exact hperm (congrArg Subtype.val h)
  have hKleH : K ≤ H := by
    let : IsKleinFour K := alternatingGroup.kleinFour_isKleinFour (by simp)
    let : Fintype K := Fintype.ofFinite K
    let ky : K := ⟨a4y, hyK⟩
    let ky' : K := ⟨y', hy'K⟩
    have hky : ky ≠ 1 := by
      intro h
      exact hy_ne (congrArg Subtype.val h)
    have hky' : ky' ≠ 1 := by
      intro h
      exact hy'_ne (congrArg Subtype.val h)
    have hkyky' : ky ≠ ky' := by
      intro h
      exact hyy' (congrArg Subtype.val h)
    intro k hk
    let kk : K := ⟨k, hk⟩
    have hmem : kk ∈ ({ky * ky', ky, ky', 1} : Finset K) := by
      rw [IsKleinFour.eq_finset_univ hky hky' hkyky']
      exact Finset.mem_univ kk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hmul | hy0 | hy'0 | h1
    · have hv : k = a4y * y' := by
        simpa [kk, ky, ky'] using congrArg Subtype.val hmul
      rw [hv]
      exact H.mul_mem hyH hy'H
    · have hv : k = a4y := by
        simpa [kk, ky] using congrArg Subtype.val hy0
      rw [hv]
      exact hyH
    · have hv : k = y' := by
        simpa [kk, ky'] using congrArg Subtype.val hy'0
      rw [hv]
      exact hy'H
    · have hv : k = 1 := by
        simpa [kk] using congrArg Subtype.val h1
      rw [hv]
      exact H.one_mem
  have hx_not_K : a4x ∉ K := by
    intro hxK
    let : IsKleinFour K := alternatingGroup.kleinFour_isKleinFour (by simp)
    have hsqK : (⟨a4x, hxK⟩ : K) * ⟨a4x, hxK⟩ = 1 :=
      IsKleinFour.mul_self (⟨a4x, hxK⟩ : K)
    have hsq : a4x * a4x = 1 := congrArg Subtype.val hsqK
    have hperm : ((a4x * a4x : alternatingGroup (Fin 4)) :
        Equiv.Perm (Fin 4)) ≠ 1 := by
      decide
    exact hperm (by simpa using congrArg Subtype.val hsq)
  have hKcard : Nat.card K = 4 := by
    dsimp [K]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  have hAcard : Nat.card (alternatingGroup (Fin 4)) = 12 :=
    alternatingGroup.card_of_card_eq_four (by simp)
  have h4dvdH : 4 ∣ Nat.card H := by
    have hd : Nat.card K ∣ Nat.card H :=
      Subgroup.card_dvd_of_le (H := K) (K := H) hKleH
    simpa only [hKcard] using hd
  have hHd12 : Nat.card H ∣ 12 := by
    rw [← hAcard]
    simpa only [Subgroup.card_top] using
      (Subgroup.card_dvd_of_le (H := H)
        (K := (⊤ : Subgroup (alternatingGroup (Fin 4)))) le_top)
  have hHcases : Nat.card H = 4 ∨ Nat.card H = 12 := by
    have hpos : 0 < Nat.card H := Nat.card_pos
    have hle : Nat.card H ≤ 12 := Nat.le_of_dvd (by norm_num) hHd12
    rcases h4dvdH with ⟨a, ha⟩
    rcases hHd12 with ⟨b, hb⟩
    interval_cases hc : Nat.card H <;> norm_num at ha hb ⊢ <;> omega
  rcases hHcases with hH4 | hH12
  · have hKH : K = H := by
      let K' : Subgroup H := K.subgroupOf H
      have hK'card : Nat.card K' = 4 := by
        calc
          Nat.card K' = Nat.card K := by
            simpa [K'] using
              Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKleH).toEquiv
          _ = 4 := hKcard
      have hidx : K'.index = 1 := by
        have hi := K'.index_mul_card
        rw [hK'card, hH4] at hi
        omega
      have hK'top : K' = ⊤ := Subgroup.index_eq_one.mp hidx
      apply le_antisymm hKleH
      intro z hz
      have hz' : (⟨z, hz⟩ : H) ∈ K' := by
        rw [hK'top]
        trivial
      exact hz'
    exact (hx_not_K (hKH ▸ hxH)).elim
  · have hidx : H.index = 1 := by
      have hi := H.index_mul_card
      rw [hH12, hAcard] at hi
      omega
    exact Subgroup.index_eq_one.mp hidx

private theorem a4_aut_eval_injective :
    Function.Injective
      (fun φ : MulAut (alternatingGroup (Fin 4)) => (φ a4x, φ a4y)) := by
  intro φ ψ h
  have hx : φ a4x = ψ a4x := congrArg Prod.fst h
  have hy : φ a4y = ψ a4y := congrArg Prod.snd h
  let E : Subgroup (alternatingGroup (Fin 4)) :=
    { carrier := {z | φ z = ψ z}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change φ a = ψ a at ha
        change φ b = ψ b at hb
        change φ (a * b) = ψ (a * b)
        rw [map_mul, map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        change φ a = ψ a at ha
        change φ (a⁻¹) = ψ (a⁻¹)
        rw [map_inv, map_inv, ha] }
  have hgen : ({a4x, a4y} : Set (alternatingGroup (Fin 4))) ⊆ E := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have htop : E = ⊤ := by
    have hle :
        Subgroup.closure ({a4x, a4y} : Set (alternatingGroup (Fin 4))) ≤ E :=
      (Subgroup.closure_le E).mpr hgen
    rw [a4x_a4y_generate] at hle
    exact le_antisymm le_top hle
  apply MulEquiv.ext
  intro z
  have hz : z ∈ E := by rw [htop]; trivial
  exact hz

/-- The conjugation map `S₄ → Aut(A₄)` is bijective. -/
public theorem aut_alternatingGroup_four_bijective_conj :
    Function.Bijective
      (MulAut.conjNormal (H := alternatingGroup (Fin 4)) :
        Equiv.Perm (Fin 4) →* MulAut (alternatingGroup (Fin 4))) := by
  let X : Finset (alternatingGroup (Fin 4)) :=
    Finset.univ.filter fun g => orderOf g = 3
  let Y : Finset (alternatingGroup (Fin 4)) :=
    Finset.univ.filter fun g => orderOf g = 2
  let ev : MulAut (alternatingGroup (Fin 4)) → X × Y := fun φ =>
    ⟨⟨φ a4x, by
        simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (φ.orderOf_eq a4x).trans a4x_order⟩,
      ⟨φ a4y, by
        simp only [Y, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (φ.orderOf_eq a4y).trans a4y_order⟩⟩
  have hev : Function.Injective ev := by
    intro φ ψ h
    apply a4_aut_eval_injective
    apply Prod.ext
    · exact congrArg (fun z => z.1.1) h
    · exact congrArg (fun z => z.2.1) h
  have hX : Nat.card X = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    simpa [X] using a4_card_order_three
  have hY : Nat.card Y = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    simpa [Y] using a4_card_order_two
  have hAutLe : Nat.card (MulAut (alternatingGroup (Fin 4))) ≤ 24 := by
    calc
      Nat.card (MulAut (alternatingGroup (Fin 4))) ≤ Nat.card (X × Y) :=
        Nat.card_le_card_of_injective ev hev
      _ = Nat.card X * Nat.card Y := by rw [Nat.card_prod]
      _ = 24 := by rw [hX, hY]
  let c : Equiv.Perm (Fin 4) →* MulAut (alternatingGroup (Fin 4)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 4))
  have hcInj : Function.Injective c :=
    conjNormal_injective_alternatingGroup 4 (by norm_num)
  have hS4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have hAutGe : 24 ≤ Nat.card (MulAut (alternatingGroup (Fin 4))) := by
    rw [← hS4]
    exact Nat.card_le_card_of_injective c hcInj
  have hcard : Nat.card (Equiv.Perm (Fin 4)) =
      Nat.card (MulAut (alternatingGroup (Fin 4))) := by omega
  exact (Nat.bijective_iff_injective_and_card c).2 ⟨hcInj, hcard⟩

end CFSG.GroupTheory.AutAlternating

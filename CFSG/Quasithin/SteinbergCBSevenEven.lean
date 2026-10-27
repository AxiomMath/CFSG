module

public import CFSG.Quasithin.SteinbergCBSevenSylowAFive

public section

namespace CFSG.Quasithin.SteinbergCB

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

theorem two_mul_card_inf_alternatingGroup {α : Type*} [Fintype α] [DecidableEq α]
    {H : Subgroup (Perm α)} {t : Perm α} (ht : t ∈ H) (hsign : sign t = -1) :
    2 * Nat.card (H ⊓ alternatingGroup α : Subgroup (Perm α)) = Nat.card H := by
  classical
  let e : {h : H // sign (h : Perm α) = 1} ≃ {h : H // ¬ sign (h : Perm α) = 1} :=
    { toFun := fun h => ⟨⟨t * h.1, H.mul_mem ht h.1.2⟩, by
        rw [map_mul, hsign, h.2]
        decide⟩
      invFun := fun h => ⟨⟨t⁻¹ * h.1, H.mul_mem (H.inv_mem ht) h.1.2⟩, by
        have h2 : sign (h.1 : Perm α) = -1 := (Int.units_eq_one_or _).resolve_left h.2
        rw [map_mul, map_inv, hsign, h2]
        decide⟩
      left_inv := fun h => by
        apply Subtype.ext
        apply Subtype.ext
        change t⁻¹ * (t * h.1) = h.1
        group
      right_inv := fun h => by
        apply Subtype.ext
        apply Subtype.ext
        change t * (t⁻¹ * h.1) = h.1
        group }
  have h1 := Fintype.card_subtype_compl (fun h : H => sign (h : Perm α) = 1)
  have h2 : Fintype.card {h : H // sign (h : Perm α) = 1} ≤ Fintype.card H :=
    Fintype.card_subtype_le _
  have h3 : Nat.card (H ⊓ alternatingGroup α : Subgroup (Perm α)) =
      Fintype.card {h : H // sign (h : Perm α) = 1} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun g => ⟨⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩, (Subgroup.mem_inf.1 g.2).2⟩
        invFun := fun h => ⟨h.1.1, Subgroup.mem_inf.2 ⟨h.1.2, h.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← Fintype.card_congr e] at h1
  rw [h3, Nat.card_eq_fintype_card]
  omega

theorem sign_swap_zero_one_seven : sign (swap 0 1 : Perm (Fin 7)) = -1 :=
  sign_swap (by decide)

theorem nat_card_sevenA_even : Nat.card (sevenA ⊓ alternatingGroup (Fin 7) : Subgroup _) = 72 := by
  have h := two_mul_card_inf_alternatingGroup (mem_sevenA.2 sevenCond_swap01.1)
    sign_swap_zero_one_seven
  rw [nat_card_sevenA] at h
  omega

theorem nat_card_sevenB_even : Nat.card (sevenB ⊓ alternatingGroup (Fin 7) : Subgroup _) = 24 := by
  have h := two_mul_card_inf_alternatingGroup (mem_sevenB.2 sevenCond_swap01.2)
    sign_swap_zero_one_seven
  rw [nat_card_sevenB] at h
  omega

theorem nat_card_sevenP_even : Nat.card (sevenP ⊓ alternatingGroup (Fin 7) : Subgroup _) = 8 := by
  have h := two_mul_card_inf_alternatingGroup (H := sevenP) (subset_closure (by simp))
    sign_swap_zero_one_seven
  rw [nat_card_sevenP] at h
  omega

theorem cycle_zero_one_six_mem_sevenA :
    (swap 0 6 * swap 0 1 : Perm (Fin 7)) • ({2, 3, 4, 5} : Finset (Fin 7)) = {2, 3, 4, 5} := by
  decide +kernel

theorem swap23_swap45_mem_sevenA :
    (swap 2 3 * swap 4 5 : Perm (Fin 7)) • ({2, 3, 4, 5} : Finset (Fin 7)) = {2, 3, 4, 5} := by
  decide +kernel

theorem swap24_swap35_mem_sevenA :
    (swap 2 4 * swap 3 5 : Perm (Fin 7)) • ({2, 3, 4, 5} : Finset (Fin 7)) = {2, 3, 4, 5} := by
  decide +kernel

theorem swap25_swap34_mem_sevenA :
    (swap 2 5 * swap 3 4 : Perm (Fin 7)) • ({2, 3, 4, 5} : Finset (Fin 7)) = {2, 3, 4, 5} := by
  decide +kernel

theorem swap02_swap13_mem_sevenB : (swap 0 2 * swap 1 3 : Perm (Fin 7)) • (6 : Fin 7) = 6 ∧
    (swap 0 2 * swap 1 3 : Perm (Fin 7)) • ({{0, 1}, {2, 3}, {4, 5}} : Finset (Finset (Fin 7))) =
      {{0, 1}, {2, 3}, {4, 5}} := by
  decide +kernel

theorem A7_two_solvable_even_overgroups_generate_A7 :
    Group.IsSolvable (sevenA ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) ∧
      Group.IsSolvable (sevenB ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) ∧
      Nat.card (sevenA ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) = 72 ∧
      Nat.card (sevenB ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) = 24 ∧
      (sevenA ⊓ alternatingGroup (Fin 7)) ⊓ (sevenB ⊓ alternatingGroup (Fin 7)) =
        sevenP ⊓ alternatingGroup (Fin 7) ∧
      Nat.card (sevenP ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) = 8 ∧
      (sevenA ⊓ alternatingGroup (Fin 7)) ⊔ (sevenB ⊓ alternatingGroup (Fin 7)) =
        alternatingGroup (Fin 7) := by
  have hA := isSolvable_sevenA
  have hB := isSolvable_sevenB
  refine ⟨Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left),
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left),
    nat_card_sevenA_even, nat_card_sevenB_even, ?_, nat_card_sevenP_even, ?_⟩
  · rw [← inf_inf_distrib_right, sevenA_inf_sevenB]
  · set G := (sevenA ⊓ alternatingGroup (Fin 7)) ⊔ (sevenB ⊓ alternatingGroup (Fin 7)) with hG
    refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
    have memA : ∀ g : Perm (Fin 7), g • ({2, 3, 4, 5} : Finset (Fin 7)) = {2, 3, 4, 5} →
        sign g = 1 → g ∈ G := fun g h1 h2 =>
      Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨mem_sevenA.2 h1, mem_alternatingGroup.2 h2⟩)
    have mc : (swap 0 6 * swap 0 1 : Perm (Fin 7)) ∈ G :=
      memA _ cycle_zero_one_six_mem_sevenA (by decide)
    have m1 : (swap 2 3 * swap 4 5 : Perm (Fin 7)) ∈ G :=
      memA _ swap23_swap45_mem_sevenA (by decide)
    have m2 : (swap 2 4 * swap 3 5 : Perm (Fin 7)) ∈ G :=
      memA _ swap24_swap35_mem_sevenA (by decide)
    have m3 : (swap 2 5 * swap 3 4 : Perm (Fin 7)) ∈ G :=
      memA _ swap25_swap34_mem_sevenA (by decide)
    have mb : (swap 0 2 * swap 1 3 : Perm (Fin 7)) ∈ G :=
      Subgroup.mem_sup_right (Subgroup.mem_inf.2
        ⟨mem_sevenB.2 swap02_swap13_mem_sevenB, mem_alternatingGroup.2 (by decide)⟩)
    have hword : ∀ y : Fin 7, ∃ g ∈ G, g 0 = y := by
      intro y
      fin_cases y
      · exact ⟨1, one_mem _, rfl⟩
      · exact ⟨_, mc, by decide⟩
      · exact ⟨_, mb, by decide⟩
      · exact ⟨_, mul_mem m1 mb, by decide⟩
      · exact ⟨_, mul_mem m2 mb, by decide⟩
      · exact ⟨_, mul_mem m3 mb, by decide⟩
      · exact ⟨_, mul_mem mc mc, by decide⟩
    have : MulAction.IsPretransitive G (Fin 7) := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨g, hg, hgx⟩ := hword x
      obtain ⟨h, hh, hhy⟩ := hword y
      refine ⟨⟨h * g⁻¹, mul_mem hh (inv_mem hg)⟩, ?_⟩
      rw [Subgroup.mk_smul, Perm.smul_def, Perm.mul_apply, Perm.inv_eq_iff_eq.2 hgx.symm, hhy]
    have h7 : (Nat.card (Fin 7)).Prime := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    have hprim : MulAction.IsPreprimitive G (Fin 7) := MulAction.IsPreprimitive.of_prime_card h7
    have h3 : IsThreeCycle (swap 0 6 * swap 0 1 : Perm (Fin 7)) :=
      isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
    exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 mc

end CFSG.Quasithin.SteinbergCB

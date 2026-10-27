module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Main
public import CFSG.Sporadic.Schreier.ClassSum

public section

namespace CFSG.Sporadic.HNSchreier

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.SideF4
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.ONSchreier

noncomputable def hnNinePermHom : A5WrTwo →* Equiv.Perm (Fin 10) :=
  (Equiv.permCongrHom pt10.symm).toMonoidHom.comp
    (RegularWreathProduct.toPerm (alternatingGroup (Fin 5)) (Multiplicative (ZMod 2)) (Fin 5))

@[expose] noncomputable def hnNineBaseW (v1 v2 : alternatingGroup (Fin 5)) : A5WrTwo :=
  ⟨fun q => if q = 1 then v1 else v2, 1⟩

noncomputable def hnNinePerm (w : A5WrTwo) : Equiv.Perm (Fin 10) := hnNinePermHom w

theorem hnNinePerm_apply (w : A5WrTwo) (x : Fin 10) :
    hnNinePerm w x = pt10.symm (MulAction.toPerm w (pt10 x)) := by
  have h : RegularWreathProduct.toPerm (alternatingGroup (Fin 5))
      (Multiplicative (ZMod 2)) (Fin 5) w = MulAction.toPerm w := rfl
  simp [hnNinePerm, hnNinePermHom, h, Equiv.permCongr_apply]

theorem hnNinePermHom_injective : Function.Injective hnNinePermHom := by
  have h1 : Function.Injective (RegularWreathProduct.toPerm (alternatingGroup (Fin 5))
      (Multiplicative (ZMod 2)) (Fin 5)) :=
    RegularWreathProduct.toPermInj (alternatingGroup (Fin 5)) (Multiplicative (ZMod 2)) (Fin 5)
  have h2 : Function.Injective (Equiv.permCongrHom pt10.symm).toMonoidHom :=
    (Equiv.permCongrHom pt10.symm).injective
  simpa [hnNinePermHom] using h2.comp h1

theorem card_range_hnNinePerm : Nat.card hnNinePermHom.range = 7200 := by
  have hcard : Nat.card hnNinePermHom.range = Nat.card A5WrTwo :=
    (Nat.card_congr (Equiv.ofInjective hnNinePermHom hnNinePermHom_injective)).symm
  rw [hcard]
  have hD : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hQ : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  rw [RegularWreathProduct.card, hD, hQ]
  norm_num

theorem hnNinePerm_mem (w : A5WrTwo) : hnNinePerm w ∈ hnNinePermHom.range :=
  ⟨w, rfl⟩

@[expose] def hnNinePRev : Equiv.Perm (Fin 5) :=
  ⟨![4, 3, 2, 1, 0], ![4, 3, 2, 1, 0], by decide, by decide⟩
theorem hnNinePRev_mem : hnNinePRev ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

@[expose] def hnNineP4A : Equiv.Perm (Fin 5) :=
  ⟨![4, 3, 1, 0, 2], ![3, 2, 4, 1, 0], by decide, by decide⟩
theorem hnNineP4A_mem : hnNineP4A ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

@[expose] def hnNineP4B : Equiv.Perm (Fin 5) :=
  ⟨![3, 2, 4, 1, 0], ![4, 3, 1, 0, 2], by decide, by decide⟩
theorem hnNineP4B_mem : hnNineP4B ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

@[expose] def hnNineP6A : Equiv.Perm (Fin 5) :=
  ⟨![0, 1, 3, 4, 2], ![0, 1, 4, 2, 3], by decide, by decide⟩
theorem hnNineP6A_mem : hnNineP6A ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

@[expose] def hnNineP6B : Equiv.Perm (Fin 5) :=
  ⟨![2, 0, 1, 3, 4], ![1, 2, 0, 3, 4], by decide, by decide⟩
theorem hnNineP6B_mem : hnNineP6B ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

@[expose] def hnNineP7A : Equiv.Perm (Fin 5) :=
  ⟨![0, 1, 4, 2, 3], ![0, 1, 3, 4, 2], by decide, by decide⟩
theorem hnNineP7A_mem : hnNineP7A ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

@[expose] def hnNineP7B : Equiv.Perm (Fin 5) :=
  ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩
theorem hnNineP7B_mem : hnNineP7B ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

@[expose] def hnNineP8 : Equiv.Perm (Fin 5) :=
  ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by decide, by decide⟩
theorem hnNineP8_mem : hnNineP8 ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

@[expose] def hnNineP9B : Equiv.Perm (Fin 5) :=
  ⟨![4, 3, 0, 2, 1], ![2, 4, 3, 1, 0], by decide, by decide⟩
theorem hnNineP9B_mem : hnNineP9B ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

@[expose] def hnNineMkW (A B : Equiv.Perm (Fin 5)) (hA : A ∈ alternatingGroup (Fin 5))
    (hB : B ∈ alternatingGroup (Fin 5)) (s : Bool) : A5WrTwo :=
  if s then ⟨fun q => if q = 1 then ⟨B, hB⟩ else ⟨A, hA⟩, Multiplicative.ofAdd 1⟩
  else ⟨fun q => if q = 1 then ⟨A, hA⟩ else ⟨B, hB⟩, 1⟩

@[expose] def hnNineWk (k : ℕ) : A5WrTwo :=
  match k with
  | 0 => hnNineMkW 1 1 (Subgroup.one_mem _) (Subgroup.one_mem _) false
  | 1 => hnNineMkW 1 1 (Subgroup.one_mem _) (Subgroup.one_mem _) false
  | 2 => hnNineMkW 1 1 (Subgroup.one_mem _) (Subgroup.one_mem _) false
  | 3 => hnNineMkW hnNinePRev hnNinePRev hnNinePRev_mem hnNinePRev_mem true
  | 4 => hnNineMkW hnNineP4A hnNineP4B hnNineP4A_mem hnNineP4B_mem true
  | 5 => hnNineMkW hnNinePRev hnNinePRev hnNinePRev_mem hnNinePRev_mem true
  | 6 => hnNineMkW hnNineP6A hnNineP6B hnNineP6A_mem hnNineP6B_mem false
  | 7 => hnNineMkW hnNineP7A hnNineP7B hnNineP7A_mem hnNineP7B_mem false
  | 8 => hnNineMkW hnNineP8 hnNineP8 hnNineP8_mem hnNineP8_mem true
  | 9 => hnNineMkW hnNinePRev hnNineP9B hnNinePRev_mem hnNineP9B_mem false
  | _ => 1

theorem hnNineWk_spec (k : Fin 10) (x : Fin 10) :
    ((pt10.symm (MulAction.toPerm (hnNineWk (k : ℕ)) (pt10 x)) : Fin 10) : ℕ)
      = (sigArrs[(k : ℕ)]!)[(x : ℕ)]! := by
  revert k x
  decide

theorem sigPerm_eq_hnNinePerm_wk
    (k : Fin 10) :
    sigPerm (k : ℕ) = hnNinePerm (hnNineWk (k : ℕ)) := by
  apply PRep.unique (prep_sigPerm k.2)
  intro x
  change (sigArrs[(k : ℕ)]!)[(x : ℕ)]! = (hnNinePerm (hnNineWk (k : ℕ)) x).val
  rw [hnNinePerm_apply]
  exact (hnNineWk_spec k x).symm



end CFSG.Sporadic.HNSchreier

namespace CFSG.Sporadic.HNSchreier

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.SideF4
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.ONSchreier

theorem phiQ_range_eq :
    phiQ.range = hnNinePermHom.range := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [range_phi_eq, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨hnNineWk k, (sigPerm_eq_hnNinePerm_wk k).symm⟩
  · rw [card_range_phi, card_range_hnNinePerm]

theorem hnNinePerm_mem_phiQ
    (w : A5WrTwo) : hnNinePerm w ∈ phiQ.range := by
  rw [phiQ_range_eq]
  exact hnNinePerm_mem w

@[expose] def hnNineA : Equiv.Perm (Fin 10) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def hnNineB : Equiv.Perm (Fin 10) := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def hnNineC : Equiv.Perm (Fin 10) := Equiv.swap 5 6 * Equiv.swap 7 8

@[expose] def hnNineD : Equiv.Perm (Fin 10) := Equiv.swap 5 7 * Equiv.swap 6 8

@[expose] def hnNineT : Equiv.Perm (Fin 10) :=
  Equiv.swap 0 5 * Equiv.swap 1 6 * Equiv.swap 2 7 * Equiv.swap 3 8 * Equiv.swap 4 9

@[expose] def hnNineX : Equiv.Perm (Fin 10) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def hnNineY : Equiv.Perm (Fin 10) := Equiv.swap 5 6 * Equiv.swap 6 7

theorem hnNineA_eq : hnNineA = hnNinePerm (hnNineBaseW
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    ⟨1, Subgroup.one_mem _⟩) := by
  ext x
  fin_cases x <;> decide

theorem hnNineB_eq : hnNineB = hnNinePerm (hnNineBaseW
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    ⟨1, Subgroup.one_mem _⟩) := by
  ext x
  fin_cases x <;> decide

theorem hnNineC_eq : hnNineC = hnNinePerm (hnNineBaseW
    ⟨1, Subgroup.one_mem _⟩
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide⟩) := by
  ext x
  fin_cases x <;> decide

theorem hnNineD_eq : hnNineD = hnNinePerm (hnNineBaseW
    ⟨1, Subgroup.one_mem _⟩
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide⟩) := by
  ext x
  fin_cases x <;> decide

theorem hnNineT_eq : hnNineT = hnNinePerm ⟨fun _ => 1, Multiplicative.ofAdd 1⟩ := by
  ext x
  fin_cases x <;> decide

theorem hnNineA_mem :
    hnNineA ∈ phiQ.range := by
  rw [hnNineA_eq]; exact hnNinePerm_mem_phiQ _

theorem hnNineB_mem :
    hnNineB ∈ phiQ.range := by
  rw [hnNineB_eq]; exact hnNinePerm_mem_phiQ _

theorem hnNineC_mem :
    hnNineC ∈ phiQ.range := by
  rw [hnNineC_eq]; exact hnNinePerm_mem_phiQ _

theorem hnNineD_mem :
    hnNineD ∈ phiQ.range := by
  rw [hnNineD_eq]; exact hnNinePerm_mem_phiQ _

theorem hnNineT_mem :
    hnNineT ∈ phiQ.range := by
  rw [hnNineT_eq]; exact hnNinePerm_mem_phiQ _

theorem hnNineX_eq : hnNineX = hnNinePerm (hnNineBaseW
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    ⟨1, Subgroup.one_mem _⟩) := by
  ext x
  fin_cases x <;> decide

theorem hnNineY_eq : hnNineY = hnNinePerm (hnNineBaseW
    ⟨1, Subgroup.one_mem _⟩
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
      rw [Equiv.Perm.mem_alternatingGroup]; decide⟩) := by
  ext x
  fin_cases x <;> decide

end CFSG.Sporadic.HNSchreier

namespace CFSG.Sporadic.HNSchreier

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.SideF4
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.ONSchreier

@[expose] def hnNineGens : List (Equiv.Perm (Fin 10)) :=
  [hnNineA, hnNineB, hnNineC, hnNineD, hnNineT]

@[expose] def hnNineList : List (Equiv.Perm (Fin 10)) :=
  [1, hnNineC, hnNineD, hnNineC * hnNineD,
   hnNineA, hnNineA * hnNineC, hnNineA * hnNineD, hnNineA * (hnNineC * hnNineD),
   hnNineB, hnNineB * hnNineC, hnNineB * hnNineD, hnNineB * (hnNineC * hnNineD),
   hnNineA * hnNineB, hnNineA * hnNineB * hnNineC, hnNineA * hnNineB * hnNineD,
   hnNineA * hnNineB * (hnNineC * hnNineD),
   hnNineT, hnNineC * hnNineT, hnNineD * hnNineT, hnNineC * hnNineD * hnNineT,
   hnNineA * hnNineT, hnNineA * hnNineC * hnNineT, hnNineA * hnNineD * hnNineT,
   hnNineA * (hnNineC * hnNineD) * hnNineT,
   hnNineB * hnNineT, hnNineB * hnNineC * hnNineT, hnNineB * hnNineD * hnNineT,
   hnNineB * (hnNineC * hnNineD) * hnNineT,
   hnNineA * hnNineB * hnNineT, hnNineA * hnNineB * hnNineC * hnNineT,
   hnNineA * hnNineB * hnNineD * hnNineT, hnNineA * hnNineB * (hnNineC * hnNineD) * hnNineT]

theorem hnNineList_length : hnNineList.length = 32 := by decide

theorem hnNineList_nodup : hnNineList.Nodup := by decide

theorem hnNineList_mul :
    hnNineList.all (fun x => hnNineList.all (fun y => decide (x * y ∈ hnNineList))) = true := by
  decide

theorem hnNineList_inv : hnNineList.all (fun x => decide (x⁻¹ ∈ hnNineList)) = true := by decide

@[expose] noncomputable def hnNineU0 : Subgroup (Equiv.Perm (Fin 10)) :=
  Subgroup.closure {x | x ∈ hnNineGens}

theorem hnNineU0_le_range :
    hnNineU0 ≤ phiQ.range := by
  rw [hnNineU0, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  simp only [hnNineGens, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [hnNineA_mem, hnNineB_mem, hnNineC_mem, hnNineD_mem, hnNineT_mem]

theorem hnNineGens_subset_list : ∀ x ∈ hnNineGens, x ∈ hnNineList := by
  intro x hx
  simp only [hnNineGens, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [hnNineList]

@[expose] noncomputable def hnNineListSub : Subgroup (Equiv.Perm (Fin 10)) where
  carrier := {x | x ∈ hnNineList}
  one_mem' := by
    change (1 : Equiv.Perm (Fin 10)) ∈ hnNineList
    simp [hnNineList]
  mul_mem' := by
    intro x y hx hy
    have h := List.all_eq_true.1 hnNineList_mul x hx
    exact of_decide_eq_true (List.all_eq_true.1 h y hy)
  inv_mem' := by
    intro x hx
    exact of_decide_eq_true (List.all_eq_true.1 hnNineList_inv x hx)

theorem hnNineU0_le_listSub : hnNineU0 ≤ hnNineListSub := by
  rw [hnNineU0, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  exact hnNineGens_subset_list x hx

theorem hnNineA_mem_U0 : hnNineA ∈ hnNineU0 :=
  Subgroup.subset_closure (by simp [hnNineGens])

theorem hnNineB_mem_U0 : hnNineB ∈ hnNineU0 :=
  Subgroup.subset_closure (by simp [hnNineGens])

theorem hnNineC_mem_U0 : hnNineC ∈ hnNineU0 :=
  Subgroup.subset_closure (by simp [hnNineGens])

theorem hnNineD_mem_U0 : hnNineD ∈ hnNineU0 :=
  Subgroup.subset_closure (by simp [hnNineGens])

theorem hnNineT_mem_U0 : hnNineT ∈ hnNineU0 :=
  Subgroup.subset_closure (by simp [hnNineGens])

theorem hnNineList_mem_U0 : ∀ x ∈ hnNineList, x ∈ hnNineU0 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_get.mp hx
  fin_cases i <;> simp only [hnNineList, List.get]
  · exact Subgroup.one_mem _
  · exact hnNineC_mem_U0
  · exact hnNineD_mem_U0
  · exact Subgroup.mul_mem _ (hnNineC_mem_U0) (hnNineD_mem_U0)
  · exact hnNineA_mem_U0
  · exact Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineC_mem_U0)
  · exact Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineD_mem_U0)
  · exact Subgroup.mul_mem _ (hnNineA_mem_U0) (Subgroup.mul_mem _ (hnNineC_mem_U0) (hnNineD_mem_U0))
  · exact hnNineB_mem_U0
  · exact Subgroup.mul_mem _ (hnNineB_mem_U0) (hnNineC_mem_U0)
  · exact Subgroup.mul_mem _ (hnNineB_mem_U0) (hnNineD_mem_U0)
  · exact Subgroup.mul_mem _ (hnNineB_mem_U0) (Subgroup.mul_mem _ (hnNineC_mem_U0) (hnNineD_mem_U0))
  · exact Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineB_mem_U0)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineB_mem_U0)) (hnNineC_mem_U0)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineB_mem_U0)) (hnNineD_mem_U0)
  · refine Subgroup.mul_mem _
      (Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineB_mem_U0))
      (Subgroup.mul_mem _ (hnNineC_mem_U0) (hnNineD_mem_U0))
  · exact hnNineT_mem_U0
  · exact Subgroup.mul_mem _ (hnNineC_mem_U0) (hnNineT_mem_U0)
  · exact Subgroup.mul_mem _ (hnNineD_mem_U0) (hnNineT_mem_U0)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnNineC_mem_U0) (hnNineD_mem_U0)) (hnNineT_mem_U0)
  · exact Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineT_mem_U0)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineC_mem_U0)) (hnNineT_mem_U0)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineD_mem_U0)) (hnNineT_mem_U0)
  · refine Subgroup.mul_mem _
      (Subgroup.mul_mem _ (hnNineA_mem_U0)
        (Subgroup.mul_mem _ (hnNineC_mem_U0) (hnNineD_mem_U0)))
      (hnNineT_mem_U0)
  · exact Subgroup.mul_mem _ (hnNineB_mem_U0) (hnNineT_mem_U0)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnNineB_mem_U0) (hnNineC_mem_U0)) (hnNineT_mem_U0)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnNineB_mem_U0) (hnNineD_mem_U0)) (hnNineT_mem_U0)
  · refine Subgroup.mul_mem _
      (Subgroup.mul_mem _ (hnNineB_mem_U0)
        (Subgroup.mul_mem _ (hnNineC_mem_U0) (hnNineD_mem_U0)))
      (hnNineT_mem_U0)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineB_mem_U0)) (hnNineT_mem_U0)
  · refine Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineB_mem_U0)) (hnNineC_mem_U0))
      (hnNineT_mem_U0)
  · refine Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineB_mem_U0)) (hnNineD_mem_U0))
      (hnNineT_mem_U0)
  · refine Subgroup.mul_mem _
      (Subgroup.mul_mem _
        (Subgroup.mul_mem _ (hnNineA_mem_U0) (hnNineB_mem_U0))
        (Subgroup.mul_mem _ (hnNineC_mem_U0) (hnNineD_mem_U0)))
      (hnNineT_mem_U0)

theorem hnNineListSub_le_U0 : hnNineListSub ≤ hnNineU0 := by
  intro x hx
  exact hnNineList_mem_U0 x hx

theorem hnNineU0_card : Nat.card hnNineU0 = 32 := by
  have h1 : Nat.card hnNineU0 ≤ Nat.card hnNineListSub :=
    Nat.card_le_card_of_injective
      (fun x : hnNineU0 => (⟨x.1, hnNineU0_le_listSub x.2⟩ : hnNineListSub))
      (fun a b hab => Subtype.ext (congrArg (fun z : hnNineListSub => z.1) hab))
  have h2 : Nat.card hnNineListSub ≤ Nat.card hnNineU0 :=
    Nat.card_le_card_of_injective
      (fun x : hnNineListSub => (⟨x.1, hnNineListSub_le_U0 x.2⟩ : hnNineU0))
      (fun a b hab => Subtype.ext (congrArg (fun z : hnNineU0 => z.1) hab))
  have hlist : Nat.card hnNineListSub = 32 := by
    calc Nat.card hnNineListSub = Nat.card {x : Equiv.Perm (Fin 10) // x ∈ hnNineList} :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
            change x ∈ (hnNineListSub : Set (Equiv.Perm (Fin 10))) ↔ x ∈ hnNineList
            rfl))
      _ = Nat.card (Fin hnNineList.length) :=
          Nat.card_congr (List.Nodup.getEquiv hnNineList hnNineList_nodup).symm
      _ = hnNineList.length := Nat.card_fin _
      _ = 32 := hnNineList_length
  omega

@[expose] noncomputable def hnNineUbar :
    Subgroup phiQ.range :=
  hnNineU0.subgroupOf phiQ.range

theorem hnNineUbar_card :
    Nat.card hnNineUbar = 32 := by
  rw [hnNineUbar]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hnNineU0_le_range).toEquiv]
  exact hnNineU0_card


@[expose] def hnNineX0 : Finset (Fin 10) := {4, 9}

@[expose] def hnNineActWk (k : Fin 10) (x : Fin 10) : Fin 10 :=
  pt10.symm (MulAction.toPerm (hnNineWk (k : ℕ)) (pt10 x))

@[expose] def hnNineGenDelta : List (Fin 10 → Fin 10) := (List.finRange 10).map hnNineActWk

@[expose] def hnNineStep (S : Finset (Finset (Fin 10))) : Finset (Finset (Fin 10)) :=
  S ∪ S.biUnion (fun s => (hnNineGenDelta.map (fun g => s.image g)).toFinset)

@[expose] def hnNineOrbitBFS (n : Nat) (S : Finset (Finset (Fin 10))) :
    Finset (Finset (Fin 10)) :=
  Nat.rec S (fun _ IH => hnNineStep IH) n

theorem hnNine_orbit_card :
    (hnNineOrbitBFS 5 ({hnNineX0} : Finset (Finset (Fin 10)))).card = 25 := by
  decide +kernel


end CFSG.Sporadic.HNSchreier

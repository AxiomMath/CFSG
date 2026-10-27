module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine3CBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine3CIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.PGL29Facts

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NF3C

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Subgroup
open scoped commutatorElement

theorem card_inf_ker (G : Subgroup Y) :
    Nat.card G = Nat.card (G.map π10) * Nat.card (G ⊓ π10.ker : Subgroup Y) := by
  rw [card_eq_card_range_mul_card_ker (π10.comp G.subtype), MonoidHom.range_comp, range_subtype]
  congr 1
  have h1 : (π10.comp G.subtype).ker = π10.ker.subgroupOf G := by ext x; exact Iff.rfl
  rw [h1, ← card_map_of_injective G.subtype_injective, subgroupOf_map_subtype, inf_comm]

theorem inf_ker_eq {G : Subgroup Y} {n : ℕ} (hML : ML ≤ G) (hcard : Nat.card G ≤ n * 3)
    (himg : Nat.card (G.map π10) = n) (hn : 0 < n) : G ⊓ π10.ker = zpowers gZeta := by
  have hle : zpowers gZeta ≤ G ⊓ π10.ker :=
    zpowers_le.mpr ⟨hML gZeta_mem_ML, MonoidHom.mem_ker.mpr π10_gZeta⟩
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [card_zpowers_gZeta]
  rw [card_inf_ker G, himg] at hcard
  exact Nat.le_of_mul_le_mul_left hcard hn

theorem inf_ker_ML : ML ⊓ π10.ker = zpowers gZeta :=
  inf_ker_eq le_rfl card_ML_le (by rw [map_ML_π10, card_psl29]) (by norm_num)

theorem inf_ker_GP : GP ⊓ π10.ker = zpowers gZeta :=
  inf_ker_eq ML_le_GP card_GP_le (by rw [map_GP_π10, Out21.A6.card_pgl29]) (by norm_num)

theorem inf_ker_GM : GM ⊓ π10.ker = zpowers gZeta :=
  inf_ker_eq ML_le_GM card_GM_le (by rw [map_GM_π10, Out21.A6.card_m10]) (by norm_num)

theorem inf_ker_GA : GA ⊓ π10.ker = zpowers gZeta :=
  inf_ker_eq ML_le_GA card_GA_le (by rw [map_GA_π10, card_autA6]) (by norm_num)

theorem zpowers_gZeta_le_ML : zpowers gZeta ≤ ML := zpowers_le.mpr gZeta_mem_ML

theorem commutator_ML : ⁅ML, ML⁆ = ML := by
  refine le_antisymm (commutator_le.mpr fun x hx y hy => ?_) ?_
  · rw [commutatorElement_def]
    exact ML.mul_mem (ML.mul_mem (ML.mul_mem hx hy) (ML.inv_mem hx)) (ML.inv_mem hy)
  · intro m hm
    have hz : gZeta ∈ ⁅ML, ML⁆ := by
      rw [gZeta_eq_commutator]
      exact commutator_mem_commutator (genML_mem 0)
        (mem_ML_of_eq [1, 0, 1, 1, 1] (by decide +kernel))
    have h1 : π10 m ∈ (⁅ML, ML⁆ : Subgroup Y).map π10 := by
      rw [map_commutator, map_ML_π10,
        CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.commutator_psl29_eq_self, ← map_ML_π10]
      exact mem_map_of_mem π10 hm
    obtain ⟨c, hc, hcm⟩ := h1
    have hcML : c ∈ ML := (commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_def]
      exact ML.mul_mem (ML.mul_mem (ML.mul_mem hx hy) (ML.inv_mem hx)) (ML.inv_mem hy) :
        ⁅ML, ML⁆ ≤ ML) hc
    have h2 : m * c⁻¹ ∈ ML ⊓ π10.ker :=
      ⟨ML.mul_mem hm (ML.inv_mem hcML), MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hcm,
        mul_inv_cancel])⟩
    rw [inf_ker_ML] at h2
    have h3 : m * c⁻¹ ∈ ⁅ML, ML⁆ := (zpowers_le.mpr hz) h2
    have h4 := mul_mem h3 hc
    rwa [inv_mul_cancel_right] at h4


@[expose] def TP : Subgroup Y := closure {gMul, gSq * gSq * gInv}
@[expose] def TM : Subgroup Y := closure {gMF, gSq * gSq * gInv}
@[expose] def TA : Subgroup Y := closure {gMul, gFrob, gInv}

theorem map_closure_ι46 (S : List Y) :
    (closure {y | y ∈ S}).map ι46 = closure {g | g ∈ S.map ι46} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  simp

theorem tP_codes : ([gMul, gSq * gSq * gInv].map ι46).map (codeN 46) = tPGenC := by
  decide +kernel
theorem tP_tbl : Core.tblCheckC (List.range 46) tPGenC
    (Core.buildCodes (List.range 46) tPGenC tPTree) tPTbl = true := by decide +kernel
theorem tP_nodup : (Core.buildCodes (List.range 46) tPGenC tPTree).Nodup := by decide +kernel
theorem tP_len : (Core.buildCodes (List.range 46) tPGenC tPTree).length = 16 := by decide +kernel

theorem tM_codes : ([gMF, gSq * gSq * gInv].map ι46).map (codeN 46) = tMGenC := by
  decide +kernel
theorem tM_tbl : Core.tblCheckC (List.range 46) tMGenC
    (Core.buildCodes (List.range 46) tMGenC tMTree) tMTbl = true := by decide +kernel
theorem tM_nodup : (Core.buildCodes (List.range 46) tMGenC tMTree).Nodup := by decide +kernel
theorem tM_len : (Core.buildCodes (List.range 46) tMGenC tMTree).length = 16 := by decide +kernel

theorem tA_codes : ([gMul, gFrob, gInv].map ι46).map (codeN 46) = tAGenC := by
  decide +kernel
theorem tA_tbl : Core.tblCheckC (List.range 46) tAGenC
    (Core.buildCodes (List.range 46) tAGenC tATree) tATbl = true := by decide +kernel
theorem tA_nodup : (Core.buildCodes (List.range 46) tAGenC tATree).Nodup := by decide +kernel
theorem tA_len : (Core.buildCodes (List.range 46) tAGenC tATree).length = 32 := by decide +kernel

theorem TP_eq : TP = closure {y | y ∈ [gMul, gSq * gSq * gInv]} := by
  rw [TP]; congr 1; ext y; simp
theorem TM_eq : TM = closure {y | y ∈ [gMF, gSq * gSq * gInv]} := by
  rw [TM]; congr 1; ext y; simp
theorem TA_eq : TA = closure {y | y ∈ [gMul, gFrob, gInv]} := by
  rw [TA]; congr 1; ext y; simp

theorem card_TP : Nat.card TP = 16 := by
  rw [← card_map_of_injective ι46_injective, TP_eq, map_closure_ι46,
    card_closure_eq_of_tblN tP_codes tP_tbl tP_nodup, tP_len]

theorem card_TM : Nat.card TM = 16 := by
  rw [← card_map_of_injective ι46_injective, TM_eq, map_closure_ι46,
    card_closure_eq_of_tblN tM_codes tM_tbl tM_nodup, tM_len]

theorem card_TA : Nat.card TA = 32 := by
  rw [← card_map_of_injective ι46_injective, TA_eq, map_closure_ι46,
    card_closure_eq_of_tblN tA_codes tA_tbl tA_nodup, tA_len]

theorem isPGroup_TP : IsPGroup 2 TP := IsPGroup.of_card (n := 4) (by rw [card_TP]; norm_num)
theorem isPGroup_TM : IsPGroup 2 TM := IsPGroup.of_card (n := 4) (by rw [card_TM]; norm_num)
theorem isPGroup_TA : IsPGroup 2 TA := IsPGroup.of_card (n := 5) (by rw [card_TA]; norm_num)

theorem mem_GP {y : Y} (h : y = gAdd ∨ y = gSq ∨ y = gInv ∨ y = gMul) : y ∈ GP :=
  Subgroup.subset_closure (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h)
theorem mem_GM {y : Y} (h : y = gAdd ∨ y = gSq ∨ y = gInv ∨ y = gMF) : y ∈ GM :=
  Subgroup.subset_closure (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h)
theorem mem_GA {y : Y} (h : y = gAdd ∨ y = gSq ∨ y = gInv ∨ y = gMul ∨ y = gFrob) : y ∈ GA :=
  Subgroup.subset_closure (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h)

theorem TP_le : TP ≤ GP := by
  rw [TP, closure_le]
  rintro _ (rfl | rfl)
  · exact mem_GP (by tauto)
  · exact mul_mem (mul_mem (mem_GP (by tauto)) (mem_GP (by tauto))) (mem_GP (by tauto))

theorem TM_le : TM ≤ GM := by
  rw [TM, closure_le]
  rintro _ (rfl | rfl)
  · exact mem_GM (by tauto)
  · exact mul_mem (mul_mem (mem_GM (by tauto)) (mem_GM (by tauto))) (mem_GM (by tauto))

theorem TA_le : TA ≤ GA := by
  rw [TA, closure_le]
  rintro _ (rfl | rfl | rfl) <;> exact mem_GA (by tauto)

theorem sup_TP : ML ⊔ TP = GP := by
  refine le_antisymm (sup_le ML_le_GP TP_le) ?_
  rw [GP, closure_le]
  rintro _ (rfl | rfl | rfl | rfl)
  · exact mem_sup_left (genML_mem 0)
  · exact mem_sup_left (genML_mem 1)
  · exact mem_sup_left (genML_mem 2)
  · exact mem_sup_right (Subgroup.subset_closure (by simp))

theorem sup_TM : ML ⊔ TM = GM := by
  refine le_antisymm (sup_le ML_le_GM TM_le) ?_
  rw [GM, closure_le]
  rintro _ (rfl | rfl | rfl | rfl)
  · exact mem_sup_left (genML_mem 0)
  · exact mem_sup_left (genML_mem 1)
  · exact mem_sup_left (genML_mem 2)
  · exact mem_sup_right (Subgroup.subset_closure (by simp))

theorem sup_TA : ML ⊔ TA = GA := by
  refine le_antisymm (sup_le ML_le_GA TA_le) ?_
  rw [GA, closure_le]
  rintro _ (rfl | rfl | rfl | rfl | rfl)
  · exact mem_sup_left (genML_mem 0)
  · exact mem_sup_left (genML_mem 1)
  · exact mem_sup_left (genML_mem 2)
  · exact mem_sup_right (Subgroup.subset_closure (by simp))
  · exact mem_sup_right (Subgroup.subset_closure (by simp))

@[expose] def uP : Equiv.Perm (Fin 10) := A6Models.tAdd
@[expose] def vP : Equiv.Perm (Fin 10) :=
  A6Models.tSq * A6Models.tSq * A6Models.tSq * A6Models.tAdd * A6Models.tSq

theorem uv_comm : uP * vP = vP * uP := by decide +kernel

theorem uv_codes : [uP, vP].map (codeN 10) = [[1, 2, 0, 4, 5, 3, 7, 8, 6, 9],
    [3, 4, 5, 6, 7, 8, 0, 1, 2, 9]] := by decide +kernel
theorem uv_tbl : Core.tblCheckC (List.range 10) [[1, 2, 0, 4, 5, 3, 7, 8, 6, 9],
    [3, 4, 5, 6, 7, 8, 0, 1, 2, 9]] (Core.buildCodes (List.range 10) [[1, 2, 0, 4, 5, 3, 7, 8, 6, 9],
    [3, 4, 5, 6, 7, 8, 0, 1, 2, 9]] uvTree) uvTbl = true := by decide +kernel
theorem uv_nodup : (Core.buildCodes (List.range 10) [[1, 2, 0, 4, 5, 3, 7, 8, 6, 9],
    [3, 4, 5, 6, 7, 8, 0, 1, 2, 9]] uvTree).Nodup := by decide +kernel
theorem uv_len : (Core.buildCodes (List.range 10) [[1, 2, 0, 4, 5, 3, 7, 8, 6, 9],
    [3, 4, 5, 6, 7, 8, 0, 1, 2, 9]] uvTree).length = 9 := by decide +kernel

theorem card_uv : Nat.card (closure ({uP, vP} : Set (Equiv.Perm (Fin 10)))) = 9 := by
  have h : closure ({uP, vP} : Set (Equiv.Perm (Fin 10))) = closure {g | g ∈ [uP, vP]} := by
    congr 1; ext g; simp
  rw [h, card_closure_eq_of_tblN uv_codes uv_tbl uv_nodup, uv_len]

theorem uv_le : closure ({uP, vP} : Set (Equiv.Perm (Fin 10))) ≤ A6Models.psl29 := by
  have ha : A6Models.tAdd ∈ A6Models.psl29 := Subgroup.subset_closure (by simp)
  have hs : A6Models.tSq ∈ A6Models.psl29 := Subgroup.subset_closure (by simp)
  rw [closure_le]
  rintro _ (rfl | rfl)
  · exact ha
  · exact mul_mem (mul_mem (mul_mem (mul_mem hs hs) hs) ha) hs

theorem relIndex_uv : (closure ({uP, vP} : Set (Equiv.Perm (Fin 10)))).relIndex
    A6Models.psl29 = 40 := by
  have h := relIndex_mul_card (closure ({uP, vP} : Set (Equiv.Perm (Fin 10)))) A6Models.psl29
  rw [inf_eq_left.mpr uv_le, card_uv, card_psl29] at h
  omega

end CFSG.LocalAnalysis.WeakClosure81.NF3C

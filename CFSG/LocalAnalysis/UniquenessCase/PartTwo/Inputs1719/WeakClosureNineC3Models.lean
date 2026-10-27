module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC3ChkP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC3ChkM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC3ChkA1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC3ChkA2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC3ChkA3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC3ChkA4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC3Spec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine3CKer

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NF3C

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Subgroup CFSG.LocalAnalysis.WeakClosure81.ChkN

theorem three_dvd_ML : 3 ∣ Nat.card (ML.map ι46) := by
  rw [card_map_of_injective ι46_injective]
  have := orderOf_dvd_natCard (⟨gZeta, gZeta_mem_ML⟩ : ML)
  rwa [Subgroup.orderOf_mk, orderOf_gZeta] at this

theorem ml_gens : ∃ l : List (Equiv.Perm (Fin 46)), l.map (codeN 46) = mlGenC ∧
    ML.map ι46 = closure {x | x ∈ l} :=
  ⟨[ι46 gAdd, ι46 gSq, ι46 gInv], mlGen_codes, map_ML⟩

theorem tPLit_eq : Core.buildCodes (List.range 46) tPGenC tPTree = tPLit := by decide +kernel

theorem descT_P : DescN (TP.map ι46) tPLit := by
  rw [TP_eq, map_closure_ι46]
  obtain ⟨hmem, hsurj⟩ := mem_closure_iff_of_tblN tP_codes tP_tbl
  rw [tPLit_eq] at hmem hsurj
  exact ⟨hmem, hsurj⟩

theorem gP_codes : (([gAdd, gSq, gInv, gMul] : List Y).map ι46).map (codeN 46) = P.Gg := by
  decide +kernel

theorem GP_map : GP.map ι46 = closure {g | g ∈ ([gAdd, gSq, gInv, gMul] : List Y).map ι46} := by
  rw [← map_closure_ι46, GP]
  congr 2
  ext y
  simp

theorem amb_P : Amb (GP.map ι46) (ML.map ι46) (TP.map ι46) P.MD :=
  ⟨ml_gens, ⟨_, gP_codes, GP_map⟩, descT_P, isPGroup_TP.map ι46, map_mono TP_le,
    map_mono ML_le_GP, P.inv_ok⟩

theorem wit_P : ∀ i < P.MD.Ks.length, witOkN 46 P.MD i = true := by
  intro i hi
  have h : P.MD.Ks.length = 15 := rfl
  rw [h] at hi
  interval_cases i
  exacts [P.wit_ok_0, P.wit_ok_1, P.wit_ok_2, P.wit_ok_3, P.wit_ok_4, P.wit_ok_5, P.wit_ok_6, P.wit_ok_7, P.wit_ok_8, P.wit_ok_9, P.wit_ok_10, P.wit_ok_11, P.wit_ok_12, P.wit_ok_13, P.wit_ok_14]

theorem ent_P : ∀ en ∈ P.MD.Es, entOkN 46 P.MD en = true := by
  show ∀ en ∈ [P.En0, P.En1, P.En2, P.En3, P.En4, P.En5, P.En6, P.En7, P.En8, P.En9, P.En10, P.En11, P.En12], entOkN 46 P.MD en = true
  simp only [List.forall_mem_cons]
  exact ⟨P.ent_ok_0, P.ent_ok_1, P.ent_ok_2, P.ent_ok_3, P.ent_ok_4, P.ent_ok_5, P.ent_ok_6, P.ent_ok_7, P.ent_ok_8, P.ent_ok_9, P.ent_ok_10, P.ent_ok_11, P.ent_ok_12, fun _ h => by simp at h⟩

theorem coordModel_P : ∃ Es : Subgroup (Equiv.Perm (Fin 46)),
    Coord3.CoordModel914 (GP.map ι46) (ML.map ι46) (TP.map ι46) Es := by
  obtain ⟨Es, h, -⟩ := coordModel_of_checks amb_P three_dvd_ML wit_P ent_P P.seed_ok P.bot_ok
    P.sq_ok fun h => absurd h (by decide)
  exact ⟨Es, h⟩

theorem tMLit_eq : Core.buildCodes (List.range 46) tMGenC tMTree = tMLit := by decide +kernel

theorem descT_M : DescN (TM.map ι46) tMLit := by
  rw [TM_eq, map_closure_ι46]
  obtain ⟨hmem, hsurj⟩ := mem_closure_iff_of_tblN tM_codes tM_tbl
  rw [tMLit_eq] at hmem hsurj
  exact ⟨hmem, hsurj⟩

theorem gM_codes : (([gAdd, gSq, gInv, gMF] : List Y).map ι46).map (codeN 46) = M.Gg := by
  decide +kernel

theorem GM_map : GM.map ι46 = closure {g | g ∈ ([gAdd, gSq, gInv, gMF] : List Y).map ι46} := by
  rw [← map_closure_ι46, GM]
  congr 2
  ext y
  simp

theorem amb_M : Amb (GM.map ι46) (ML.map ι46) (TM.map ι46) M.MD :=
  ⟨ml_gens, ⟨_, gM_codes, GM_map⟩, descT_M, isPGroup_TM.map ι46, map_mono TM_le,
    map_mono ML_le_GM, M.inv_ok⟩

theorem wit_M : ∀ i < M.MD.Ks.length, witOkN 46 M.MD i = true := by
  intro i hi
  have h : M.MD.Ks.length = 7 := rfl
  rw [h] at hi
  interval_cases i
  exacts [M.wit_ok_0, M.wit_ok_1, M.wit_ok_2, M.wit_ok_3, M.wit_ok_4, M.wit_ok_5, M.wit_ok_6]

theorem ent_M : ∀ en ∈ M.MD.Es, entOkN 46 M.MD en = true := by
  show ∀ en ∈ [M.En0, M.En1, M.En2, M.En3, M.En4, M.En5, M.En6], entOkN 46 M.MD en = true
  simp only [List.forall_mem_cons]
  exact ⟨M.ent_ok_0, M.ent_ok_1, M.ent_ok_2, M.ent_ok_3, M.ent_ok_4, M.ent_ok_5, M.ent_ok_6, fun _ h => by simp at h⟩

theorem coordModel_M : ∃ Es : Subgroup (Equiv.Perm (Fin 46)),
    Coord3.CoordModel914 (GM.map ι46) (ML.map ι46) (TM.map ι46) Es := by
  obtain ⟨Es, h, -⟩ := coordModel_of_checks amb_M three_dvd_ML wit_M ent_M M.seed_ok M.bot_ok
    M.sq_ok fun h => absurd h (by decide)
  exact ⟨Es, h⟩

theorem tALit_eq : Core.buildCodes (List.range 46) tAGenC tATree = tALit := by decide +kernel

theorem descT_A : DescN (TA.map ι46) tALit := by
  rw [TA_eq, map_closure_ι46]
  obtain ⟨hmem, hsurj⟩ := mem_closure_iff_of_tblN tA_codes tA_tbl
  rw [tALit_eq] at hmem hsurj
  exact ⟨hmem, hsurj⟩

theorem gA_codes : (([gAdd, gSq, gInv, gMul, gFrob] : List Y).map ι46).map (codeN 46) = A.Gg := by
  decide +kernel

theorem GA_map : GA.map ι46 = closure {g | g ∈ ([gAdd, gSq, gInv, gMul, gFrob] : List Y).map ι46} := by
  rw [← map_closure_ι46, GA]
  congr 2
  ext y
  simp

theorem amb_A : Amb (GA.map ι46) (ML.map ι46) (TA.map ι46) A.MD :=
  ⟨ml_gens, ⟨_, gA_codes, GA_map⟩, descT_A, isPGroup_TA.map ι46, map_mono TA_le,
    map_mono ML_le_GA, A.inv_ok⟩

theorem wit_A : ∀ i < A.MD.Ks.length, witOkN 46 A.MD i = true := by
  intro i hi
  have h : A.MD.Ks.length = 36 := rfl
  rw [h] at hi
  interval_cases i
  exacts [A.wit_ok_0, A.wit_ok_1, A.wit_ok_2, A.wit_ok_3, A.wit_ok_4, A.wit_ok_5, A.wit_ok_6, A.wit_ok_7, A.wit_ok_8, A.wit_ok_9, A.wit_ok_10, A.wit_ok_11, A.wit_ok_12, A.wit_ok_13, A.wit_ok_14, A.wit_ok_15, A.wit_ok_16, A.wit_ok_17, A.wit_ok_18, A.wit_ok_19, A.wit_ok_20, A.wit_ok_21, A.wit_ok_22, A.wit_ok_23, A.wit_ok_24, A.wit_ok_25, A.wit_ok_26, A.wit_ok_27, A.wit_ok_28, A.wit_ok_29, A.wit_ok_30, A.wit_ok_31, A.wit_ok_32, A.wit_ok_33, A.wit_ok_34, A.wit_ok_35]

theorem ent_A : ∀ en ∈ A.MD.Es, entOkN 46 A.MD en = true := by
  show ∀ en ∈ [A.En0, A.En1, A.En2, A.En3, A.En4, A.En5, A.En6, A.En7, A.En8, A.En9, A.En10, A.En11, A.En12, A.En13, A.En14, A.En15, A.En16, A.En17, A.En18, A.En19, A.En20, A.En21, A.En22, A.En23, A.En24, A.En25, A.En26, A.En27, A.En28, A.En29, A.En30, A.En31], entOkN 46 A.MD en = true
  simp only [List.forall_mem_cons]
  exact ⟨A.ent_ok_0, A.ent_ok_1, A.ent_ok_2, A.ent_ok_3, A.ent_ok_4, A.ent_ok_5, A.ent_ok_6, A.ent_ok_7, A.ent_ok_8, A.ent_ok_9, A.ent_ok_10, A.ent_ok_11, A.ent_ok_12, A.ent_ok_13, A.ent_ok_14, A.ent_ok_15, A.ent_ok_16, A.ent_ok_17, A.ent_ok_18, A.ent_ok_19, A.ent_ok_20, A.ent_ok_21, A.ent_ok_22, A.ent_ok_23, A.ent_ok_24, A.ent_ok_25, A.ent_ok_26, A.ent_ok_27, A.ent_ok_28, A.ent_ok_29, A.ent_ok_30, A.ent_ok_31, fun _ h => by simp at h⟩

theorem coordModel_A : ∃ Es : Subgroup (Equiv.Perm (Fin 46)),
    Coord3.CoordModel914 (GA.map ι46) (ML.map ι46) (TA.map ι46) Es := by
  obtain ⟨Es, h, -⟩ := coordModel_of_checks amb_A three_dvd_ML wit_A ent_A A.seed_ok A.bot_ok
    A.sq_ok fun _ => A.star_ok
  exact ⟨Es, h⟩

end CFSG.LocalAnalysis.WeakClosure81.NF3C

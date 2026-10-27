module

public import CFSG.Monster.VisCert.FrameData

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisCert

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible

@[expose] def pAInvList : List ℕ :=
  [3, 4, 20, 0, 1, 13, 18, 11, 19, 16, 23, 7, 14, 5, 12, 22, 9, 21, 6, 8, 2, 17, 15, 10]

@[expose] def pBInvList : List ℕ :=
  [18, 14, 13, 0, 4, 5, 2, 17, 8, 1, 10, 19, 20, 6, 9, 12, 16, 22, 3, 23, 15, 21, 7, 11]

@[expose] def frameActN (g : ℕ) : (ℕ → ℤ) → ℕ → ℤ :=
  if g = 0 then xiN else if g = 1 then permN pAInvList else if g = 2 then permN pBInvList
  else signN (Bmask (g - 3))

@[expose] def frameRowsOK : Bool :=
  allTo (fun g => allTo (fun i => rowCheck (frameActN g (ellN i)) (frameMatrices[g]!)[i]!) 24) 15

theorem frameRowsOK_eq_true : frameRowsOK = true := by decide +kernel

theorem pA_inv_apply : ∀ i : Fin 24, ((pA⁻¹ i : Fin 24) : ℕ) = pAInvList.getD i 0 := by
  decide +kernel

theorem pB_inv_apply : ∀ i : Fin 24, ((pB⁻¹ i : Fin 24) : ℕ) = pBInvList.getD i 0 := by
  decide +kernel

theorem comp_pA_inv (U : ℕ → ℤ) :
    (fun i : Fin 24 => U i) ∘ ⇑(pA⁻¹) = fun i : Fin 24 => permN pAInvList U i := by
  funext i
  simp only [Function.comp, permN, pA_inv_apply]

theorem comp_pB_inv (U : ℕ → ℤ) :
    (fun i : Fin 24 => U i) ∘ ⇑(pB⁻¹) = fun i : Fin 24 => permN pBInvList U i := by
  funext i
  simp only [Function.comp, permN, pB_inv_apply]

private theorem frame_cases (g : Fin 15) :
    (g : ℕ) = 0 ∨ (g : ℕ) = 1 ∨ (g : ℕ) = 2 ∨ 3 ≤ (g : ℕ) := by omega

theorem frameGen_of_eq_zero {g : Fin 15} (h : (g : ℕ) = 0) : frameGen g = xiO := by
  simp [frameGen, h]

theorem frameGen_of_eq_one {g : Fin 15} (h : (g : ℕ) = 1) : frameGen g = PO pAAut := by
  simp [frameGen, h]

theorem frameGen_of_eq_two {g : Fin 15} (h : (g : ℕ) = 2) : frameGen g = PO pBAut := by
  simp [frameGen, h]

theorem frameGen_of_three_le {g : Fin 15} (h : 3 ≤ (g : ℕ)) :
    frameGen g = gO (bC ⟨g - 3, by omega⟩) := by
  simp [frameGen, show (g : ℕ) ≠ 0 by omega, show (g : ℕ) ≠ 1 by omega,
    show (g : ℕ) ≠ 2 by omega]

theorem frameActN_of_eq_zero {g : ℕ} (h : g = 0) : frameActN g = xiN := by simp [frameActN, h]

theorem frameActN_of_eq_one {g : ℕ} (h : g = 1) : frameActN g = permN pAInvList := by
  simp [frameActN, h]

theorem frameActN_of_eq_two {g : ℕ} (h : g = 2) : frameActN g = permN pBInvList := by
  simp [frameActN, h]

theorem frameActN_of_three_le {g : ℕ} (h : 3 ≤ g) : frameActN g = signN (Bmask (g - 3)) := by
  simp [frameActN, show g ≠ 0 by omega, show g ≠ 1 by omega, show g ≠ 2 by omega]

theorem frameActN_mem (g : Fin 15) {U : ℕ → ℤ}
    (hU : (fun i : Fin 24 => U i) ∈ codeLattice C) :
    (fun i : Fin 24 => frameActN g U i) ∈ codeLattice C := by
  rcases frame_cases g with h | h | h | h
  · rw [frameActN_of_eq_zero h, ← xiInt_eq_xiN]
    exact Xi.xiInt_mem hU
  · rw [frameActN_of_eq_one h, ← comp_pA_inv]
    exact comp_mem_codeLattice (inv_mem pA_mem) hU
  · rw [frameActN_of_eq_two h, ← comp_pB_inv]
    exact comp_mem_codeLattice (inv_mem pB_mem) hU
  · have e := signVec_B ⟨g - 3, by omega⟩ U
    simp only at e
    rw [frameActN_of_three_le h, ← e]
    exact signVec_mem (B_mem_C _) hU

theorem modTwoEnd_frameGen_cls (g : Fin 15) {U : ℕ → ℤ}
    (hU : (fun i : Fin 24 => U i) ∈ codeLattice C) :
    modTwoEnd (frameGen g) (cls (fun i : Fin 24 => U i) hU) =
      cls (fun i : Fin 24 => frameActN g U i) (frameActN_mem g hU) := by
  rcases frame_cases g with h | h | h | h
  · rw [frameGen_of_eq_zero h, modTwoEnd_xiO_cls_of hU (Xi.xiInt_mem hU)
      (Xi.toQ_mem_latticeQ_vecMul hU)]
    exact cls_eq_of_eq _ _ (by rw [xiInt_eq_xiN, frameActN_of_eq_zero h])
  · rw [frameGen_of_eq_one h, modTwoEnd_PO_cls]
    exact cls_eq_of_eq _ _ (by rw [frameActN_of_eq_one h]; exact comp_pA_inv U)
  · rw [frameGen_of_eq_two h, modTwoEnd_PO_cls]
    exact cls_eq_of_eq _ _ (by rw [frameActN_of_eq_two h]; exact comp_pB_inv U)
  · rw [frameGen_of_three_le h, modTwoEnd_gO_cls]
    exact cls_eq_of_eq _ _ (by
      rw [frameActN_of_three_le h]
      exact signVec_B ⟨g - 3, by omega⟩ U)

theorem modTwoEnd_frameGen_ellCls (g : Fin 15) (i : Fin 24) :
    modTwoEnd (frameGen g) (ellCls i) = dec (frameMatrices[(g : ℕ)]!)[(i : ℕ)]! := by
  rw [ellCls_eq, modTwoEnd_frameGen_cls]
  exact cls_eq_dec_of_rowCheck _ (allTo_spec (allTo_spec frameRowsOK_eq_true g.2) i.2)

theorem kGen_smul_ellCls (g : Fin 15) (i : Fin 24) :
    kGen g • ellCls i = dec (frameMatrices[(g : ℕ)]!)[(i : ℕ)]! :=
  modTwoEnd_frameGen_ellCls g i

theorem kGen_smul_dec (g : Fin 15) (v : ℕ) :
    kGen g • dec v = dec (actRows frameMatrices[(g : ℕ)]! v) := by
  rw [kGen_smul, dec_actRows, dec, map_sum]
  simp only [map_smul, modTwoEnd_frameGen_ellCls]

@[expose] def kGenN (j : ℕ) : GLV := if h : j < 15 then kGen ⟨j, h⟩ else 1

theorem kGenN_smul_dec' {g : ℕ} (hg : g < 15) (v : ℕ) :
    kGenN g • dec v = dec (actRows frameMatrices[g]! v) := by
  rw [kGenN, dite_eq_left hg]
  exact kGen_smul_dec ⟨g, hg⟩ v

theorem kGenN_mem_Kvis {g : ℕ} (hg : g < 15) : kGenN g ∈ Kvis := by
  rw [kGenN, dite_eq_left hg]
  exact Subgroup.subset_closure ⟨_, rfl⟩

theorem kGenN_mem_Nvis {g : ℕ} (hg1 : 1 ≤ g) (hg : g < 15) : kGenN g ∈ Nvis := by
  rw [kGenN, dite_eq_left hg]
  exact Subgroup.subset_closure ⟨⟨g, hg⟩, hg1, rfl⟩

@[expose] def wordGL : List ℕ → GLV
  | [] => 1
  | g :: w => wordGL w * kGenN g

theorem wordGL_smul_dec : ∀ (w : List ℕ), (∀ g ∈ w, g < 15) → ∀ v : ℕ,
    wordGL w • dec v = dec (actWord frameMatrices w v)
  | [], _, v => by simp [wordGL, actWord]
  | g :: w, hw, v => by
    have hg : g < 15 := hw g List.mem_cons_self
    rw [wordGL, mul_smul, kGenN_smul_dec' hg, actWord,
      wordGL_smul_dec w (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg'))]

theorem wordGL_mem_Kvis : ∀ (w : List ℕ), (∀ g ∈ w, g < 15) → wordGL w ∈ Kvis
  | [], _ => Kvis.one_mem
  | g :: w, hw => Kvis.mul_mem (wordGL_mem_Kvis w fun g' hg' => hw g' (List.mem_cons_of_mem _ hg'))
      (kGenN_mem_Kvis (hw g List.mem_cons_self))

theorem wordGL_mem_Nvis : ∀ (w : List ℕ), (∀ g ∈ w, 1 ≤ g ∧ g < 15) → wordGL w ∈ Nvis
  | [], _ => Nvis.one_mem
  | g :: w, hw => Nvis.mul_mem (wordGL_mem_Nvis w fun g' hg' => hw g' (List.mem_cons_of_mem _ hg'))
      (kGenN_mem_Nvis (hw g List.mem_cons_self).1 (hw g List.mem_cons_self).2)

@[expose] def frameRep (t : Fin 6) : L2 := dec fusionOrbitReps[(t : ℕ)]!

theorem frameRep_zero : frameRep 0 = twoΩCls := dec_seed

end CFSG.Monster.VisCert

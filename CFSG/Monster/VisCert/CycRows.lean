module

public import CFSG.Monster.VisCert.Data
public import CFSG.Monster.VisCert.Basis

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisCert

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible

@[expose] def xiN (U : ℕ → ℤ) (i : ℕ) : ℤ :=
  (if i % 4 = 0 then -1 else 1) *
    (U i - (U (4 * (i / 4)) + U (4 * (i / 4) + 1) + U (4 * (i / 4) + 2) + U (4 * (i / 4) + 3)) / 2)

@[expose] def permN (inv : List ℕ) (U : ℕ → ℤ) (i : ℕ) : ℤ := U (inv.getD i 0)

@[expose] def signN (m : ℕ) (U : ℕ → ℤ) (i : ℕ) : ℤ := if m.testBit i then -U i else U i

@[expose] def pInvList : List ℕ :=
  [19, 1, 0, 2, 3, 16, 17, 18, 4, 14, 9, 20, 5, 13, 11, 21, 6, 15, 10, 22, 7, 12, 8, 23]

@[expose] def cycActN (g : ℕ) : (ℕ → ℤ) → ℕ → ℤ :=
  if g = 0 then xiN else if g = 1 then permN pInvList else signN (Bmask (g - 2))

@[expose] def cycRowsOK : Bool :=
  allTo (fun g => allTo (fun i => rowCheck (cycActN g (ellN i)) (cycRows[g]!)[i]!) 24) 14

theorem cycRowsOK_eq_true : cycRowsOK = true := by decide +kernel

theorem cls_eq_of_eq {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C)
    (h : u = v) : cls u hu = cls v hv := by
  subst h
  rfl

theorem xiInt_eq_xiN (U : ℕ → ℤ) :
    Xi.xiInt (fun i : Fin 24 => U i) = fun i : Fin 24 => xiN U i := by
  funext i
  simp only [Xi.xiInt, Xi.colSum, Fin.sum_univ_four, xiN]
  fin_cases i <;> rfl

theorem pCyc_inv_apply : ∀ i : Fin 24, ((pCyc⁻¹ i : Fin 24) : ℕ) = pInvList.getD i 0 := by
  decide +kernel

theorem comp_pCyc_inv (U : ℕ → ℤ) :
    (fun i : Fin 24 => U i) ∘ ⇑(pCyc⁻¹) = fun i : Fin 24 => permN pInvList U i := by
  funext i
  simp only [Function.comp, permN, pCyc_inv_apply]

theorem signVec_B (j : Fin 12) (U : ℕ → ℤ) :
    signVec (B j) (fun i : Fin 24 => U i) = fun i : Fin 24 => signN (Bmask j) U i := by
  funext i
  rw [signVec_apply, B_eq_bvec, bvec_apply, signN]
  split_ifs
  · rw [bitLift_one]
    ring
  · rw [show bitLift (0 : ZMod 2) = 0 from rfl]
    ring

private theorem cyc_cases (g : Fin 14) : (g : ℕ) = 0 ∨ (g : ℕ) = 1 ∨ 2 ≤ (g : ℕ) := by omega

theorem cycGen_of_eq_zero {g : Fin 14} (h : (g : ℕ) = 0) : cycGen g = xiO := by
  simp [cycGen, h]

theorem cycGen_of_eq_one {g : Fin 14} (h : (g : ℕ) = 1) : cycGen g = PO pAut := by
  simp [cycGen, h]

theorem cycGen_of_two_le {g : Fin 14} (h : 2 ≤ (g : ℕ)) :
    cycGen g = gO (bC ⟨g - 2, by omega⟩) := by
  simp [cycGen, show (g : ℕ) ≠ 0 by omega, show (g : ℕ) ≠ 1 by omega]

theorem cycActN_of_eq_zero {g : ℕ} (h : g = 0) : cycActN g = xiN := by simp [cycActN, h]

theorem cycActN_of_eq_one {g : ℕ} (h : g = 1) : cycActN g = permN pInvList := by
  simp [cycActN, h]

theorem cycActN_of_two_le {g : ℕ} (h : 2 ≤ g) : cycActN g = signN (Bmask (g - 2)) := by
  simp [cycActN, show g ≠ 0 by omega, show g ≠ 1 by omega]

theorem cycActN_mem (g : Fin 14) {U : ℕ → ℤ} (hU : (fun i : Fin 24 => U i) ∈ codeLattice C) :
    (fun i : Fin 24 => cycActN g U i) ∈ codeLattice C := by
  rcases cyc_cases g with h | h | h
  · rw [cycActN_of_eq_zero h, ← xiInt_eq_xiN]
    exact Xi.xiInt_mem hU
  · rw [cycActN_of_eq_one h, ← comp_pCyc_inv]
    exact comp_mem_codeLattice (inv_mem pCyc_mem) hU
  · have e := signVec_B ⟨g - 2, by omega⟩ U
    simp only at e
    rw [cycActN_of_two_le h, ← e]
    exact signVec_mem (B_mem_C _) hU

theorem modTwoEnd_cycGen_cls (g : Fin 14) {U : ℕ → ℤ}
    (hU : (fun i : Fin 24 => U i) ∈ codeLattice C) :
    modTwoEnd (cycGen g) (cls (fun i : Fin 24 => U i) hU) =
      cls (fun i : Fin 24 => cycActN g U i) (cycActN_mem g hU) := by
  rcases cyc_cases g with h | h | h
  · rw [cycGen_of_eq_zero h, modTwoEnd_xiO_cls_of hU (Xi.xiInt_mem hU)
      (Xi.toQ_mem_latticeQ_vecMul hU)]
    exact cls_eq_of_eq _ _ (by rw [xiInt_eq_xiN, cycActN_of_eq_zero h])
  · rw [cycGen_of_eq_one h, modTwoEnd_PO_cls]
    exact cls_eq_of_eq _ _ (by rw [cycActN_of_eq_one h]; exact comp_pCyc_inv U)
  · rw [cycGen_of_two_le h, modTwoEnd_gO_cls]
    exact cls_eq_of_eq _ _ (by
      rw [cycActN_of_two_le h]
      exact signVec_B ⟨g - 2, by omega⟩ U)

theorem ellN_mem (i : Fin 24) : (fun j : Fin 24 => ellN i j) ∈ codeLattice C := by
  rw [← ellVec_eq]
  exact ellVec_mem i

theorem ellCls_eq (i : Fin 24) : ellCls i = cls (fun j : Fin 24 => ellN i j) (ellN_mem i) :=
  cls_eq_of_eq _ _ (ellVec_eq i)

theorem modTwoEnd_cycGen_ellCls (g : Fin 14) (i : Fin 24) :
    modTwoEnd (cycGen g) (ellCls i) = dec (cycRows[(g : ℕ)]!)[(i : ℕ)]! := by
  rw [ellCls_eq, modTwoEnd_cycGen_cls]
  exact cls_eq_dec_of_rowCheck _ (allTo_spec (allTo_spec cycRowsOK_eq_true g.2) i.2)

theorem modTwoEnd_cycGen_dec (g : Fin 14) (v : ℕ) :
    modTwoEnd (cycGen g) (dec v) = dec (actRows cycRows[(g : ℕ)]! v) := by
  rw [dec_actRows, dec, map_sum]
  simp only [map_smul, modTwoEnd_cycGen_ellCls]

theorem modTwoEnd_cycWordElt : ∀ (w : List ℕ), (∀ g ∈ w, g < 14) → ∀ v : ℕ,
    modTwoEnd (cycWordElt w) (dec v) = dec (actWord cycRows w v)
  | [], _, v => by simp [cycWordElt, actWord, modTwoEnd_one]
  | g :: w, hw, v => by
    have hg : g < 14 := hw g List.mem_cons_self
    have e : cycWordElt (g :: w) = cycGen ⟨g, hg⟩ * cycWordElt w := by
      simp [cycWordElt, cycGenN, hg]
    rw [e, modTwoEnd_mul, Module.End.mul_apply, modTwoEnd_cycGen_dec, actWord,
      modTwoEnd_cycWordElt w (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg'))]

end CFSG.Monster.VisCert

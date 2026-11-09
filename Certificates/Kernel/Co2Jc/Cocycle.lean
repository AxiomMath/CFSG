module

public import Certificates.Kernel.Co2Jc.CocycleK
public import Certificates.Kernel.Co2Jc.SplitRows

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelCo2Jc

open CFSG.Sporadic.Co2Jc.Native
open CFSG.Sporadic.Co2Jc.Data (rels)

theorem coc_rel : relOK = true := by
  simp only [relOK, wordActK_eq]
  decide +kernel

theorem coc_dualRowsLen : dualRowsLenOK = true := by
  simp only [dualRowsLenOK, dualRows_eq]
  decide +kernel

theorem coc_dualPLen : dualPLenOK = true := by decide +kernel

theorem coc_dualCombLen : dualCombLenOK = true := by decide +kernel

theorem coc_dualComb : dualCombOK = true := by
  simp only [dualCombOK, dualTarget, dualRows_eq, gl_eq]
  decide +kernel

theorem coc_rows0 : relRows (rels[0]!) = splitRowsDat[0]! :=
  eq_of_beq (by decide +kernel)

theorem coc_rows1 : relRows (rels[1]!) = splitRowsDat[1]! :=
  eq_of_beq (by decide +kernel)

theorem coc_rows2 : relRows (rels[2]!) = splitRowsDat[2]! :=
  eq_of_beq (by decide +kernel)

theorem coc_rows3 : relRows (rels[3]!) = splitRowsDat[3]! :=
  eq_of_beq (by decide +kernel)

theorem coc_splitRowsLen : splitRowsLenOK = true := by
  rw [splitRowsLenOK, splitRows_eq, splitRowsK_len]
  rfl

theorem coc_xmaskLen : xmaskLenOK = true := by decide +kernel

theorem coc_combSplitLen : combSplitLenOK = true := by decide +kernel

theorem coc_gamma0Len : gamma0LenOK = true := by decide +kernel

theorem coc_fixT : fixT = true := by
  simp only [fixT, gl_eq]
  decide +kernel

theorem coc_walk0 : splitSolWR 0 5 = true := by
  rw [splitSolWR]
  decide +kernel

theorem coc_walk1 : splitSolWR 5 5 = true := by
  rw [splitSolWR]
  decide +kernel

theorem coc_walk2 : splitSolWR 10 5 = true := by
  rw [splitSolWR]
  decide +kernel

theorem coc_walk3 : splitSolWR 15 5 = true := by
  rw [splitSolWR]
  decide +kernel

theorem coc_walk4 : splitSolWR 20 5 = true := by
  rw [splitSolWR]
  decide +kernel

theorem coc_splitSolW : splitSolW = true :=
  splitSolW_of_chunks fun c hc => match c, hc with
    | 0, _ => coc_walk0
    | 1, _ => coc_walk1
    | 2, _ => coc_walk2
    | 3, _ => coc_walk3
    | 4, _ => coc_walk4
    | _ + 5, h => absurd h (by omega)

theorem coc_splitSolK : splitSolK = true :=
  splitSolK_of_F (splitSolF_of_D (of_decide_eq_true coc_gamma0Len) (splitSolD_of_W coc_splitSolW))
    (of_decide_eq_true coc_gamma0Len)

theorem coc_take400 : splitRowsK.take 400 =
    splitRowsDat[0]! ++ splitRowsDat[1]! ++ splitRowsDat[2]! ++ splitRowsDat[3]! := by
  rw [splitRowsK_take400, coc_rows0, coc_rows1, coc_rows2, coc_rows3]

theorem coc_splitSol : splitSolOK = true := by
  rw [splitSol_eq splitRowsK_len]
  exact coc_splitSolK

theorem coc_noW : noW = true := by
  simp only [noW, gl_eq]
  decide +kernel

theorem coc_mask0 : splitMaskC 0 = true := by
  refine splitMaskC_of_take 400 _ ?_
  rw [coc_take400]
  simp only [splitMaskP, splitRes, cobMask, cobMask1, cobMask2, gl_eq]
  decide +kernel

theorem coc_mask1 : splitMaskC 30 = true := by
  refine splitMaskC_of_take 400 _ ?_
  rw [coc_take400]
  simp only [splitMaskP, splitRes, cobMask, cobMask1, cobMask2, gl_eq]
  decide +kernel

theorem coc_mask2 : splitMaskC 60 = true := by
  refine splitMaskC_of_take 400 _ ?_
  rw [coc_take400]
  simp only [splitMaskP, splitRes, cobMask, cobMask1, cobMask2, gl_eq]
  decide +kernel

theorem coc_mask3 : splitMaskC 90 = true := by
  refine splitMaskC_of_take 400 _ ?_
  rw [coc_take400]
  simp only [splitMaskP, splitRes, cobMask, cobMask1, cobMask2, gl_eq]
  decide +kernel

theorem coc_mask4 : splitMaskC 120 = true := by
  refine splitMaskC_of_take 400 _ ?_
  rw [coc_take400]
  simp only [splitMaskP, splitRes, cobMask, cobMask1, cobMask2, gl_eq]
  decide +kernel

theorem coc_mask5 : splitMaskC 150 = true := by
  refine splitMaskC_of_take 400 _ ?_
  rw [coc_take400]
  simp only [splitMaskP, splitRes, cobMask, cobMask1, cobMask2, gl_eq]
  decide +kernel

theorem coc_mask6 : splitMaskC 180 = true := by
  refine splitMaskC_of_take 400 _ ?_
  rw [coc_take400]
  simp only [splitMaskP, splitRes, cobMask, cobMask1, cobMask2, gl_eq]
  decide +kernel

theorem coc_mask7 : splitMaskC 210 = true := by
  refine splitMaskC_of_take 400 _ ?_
  rw [coc_take400]
  simp only [splitMaskP, splitRes, cobMask, cobMask1, cobMask2, gl_eq]
  decide +kernel

theorem coc_mask8 : splitMaskC 240 = true := by
  refine splitMaskC_of_take 400 _ ?_
  rw [coc_take400]
  simp only [splitMaskP, splitRes, cobMask, cobMask1, cobMask2, gl_eq]
  decide +kernel

theorem coc_mask9 : splitMaskC 270 = true := by
  refine splitMaskC_of_take 400 _ ?_
  rw [coc_take400]
  simp only [splitMaskP, splitRes, cobMask, cobMask1, cobMask2, gl_eq]
  decide +kernel

theorem coc_splitMask : splitMaskOK = true :=
  splitMask_of_chunks fun j hj => match j, hj with
    | 0, _ => coc_mask0
    | 1, _ => coc_mask1
    | 2, _ => coc_mask2
    | 3, _ => coc_mask3
    | 4, _ => coc_mask4
    | 5, _ => coc_mask5
    | 6, _ => coc_mask6
    | 7, _ => coc_mask7
    | 8, _ => coc_mask8
    | 9, _ => coc_mask9
    | _ + 10, h => absurd h (by omega)

theorem cocycle_check : cocycleOK = true := by
  simp only [cocycleOK, cocycleChecks, dualOK, dualChecks, splitOK, splitChecks, List.all_cons,
    List.all_nil, id, coc_rel, coc_dualRowsLen, coc_dualPLen, coc_dualCombLen, coc_dualComb,
    coc_splitRowsLen, coc_xmaskLen, coc_combSplitLen, coc_gamma0Len, coc_fixT, coc_splitSol,
    coc_noW, coc_splitMask, Bool.and_true]

end CertificateChecks.KernelCo2Jc

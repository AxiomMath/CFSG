module

public import Certificates.Kernel.Co2Jc.CocycleK

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Jc

open CFSG.Sporadic.Co2Jc.Native

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

theorem coc_splitRowsLen : splitRowsLenOK = true := by
  simp only [splitRowsLenOK, splitRows_eq]
  decide +kernel

theorem coc_xmaskLen : xmaskLenOK = true := by decide +kernel

theorem coc_combSplitLen : combSplitLenOK = true := by decide +kernel

theorem coc_gamma0Len : gamma0LenOK = true := by decide +kernel

theorem coc_fixT : fixT = true := by
  simp only [fixT, gl_eq]
  decide +kernel

theorem coc_splitSol : splitSolOK = true := by
  simp only [splitSolOK, splitRows_eq]
  decide +kernel

theorem coc_noW : noW = true := by
  simp only [noW, gl_eq]
  decide +kernel

theorem coc_splitMask : splitMaskOK = true := by
  simp only [splitMaskOK, splitRes, cobMask, cobMask1, cobMask2, splitRows_eq, gl_eq]
  decide +kernel

theorem cocycle_check : cocycleOK = true := by
  simp only [cocycleOK, cocycleChecks, dualOK, dualChecks, splitOK, splitChecks, List.all_cons,
    List.all_nil, id, coc_rel, coc_dualRowsLen, coc_dualPLen, coc_dualCombLen, coc_dualComb,
    coc_splitRowsLen, coc_xmaskLen, coc_combSplitLen, coc_gamma0Len, coc_fixT, coc_splitSol,
    coc_noW, coc_splitMask, Bool.and_true]

end CertificateChecks.KernelCo2Jc

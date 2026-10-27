module

public import Certificates.Data.R3E417.McL

public section

namespace CertificateChecks.Batch8175

open CFSG.RankThree.PartTwo.Sec4.Res417Five.McLE81

private theorem decR_oneR_0 : decR oneR = 1 := by
  decide +kernel

private theorem decode_seedA_1 :
    CFSG.Blueprint.NativeSporadic.decode 3 21 1 CFSG.Sporadic.McL.Native.seedA = decR aR := by
  decide +kernel

private theorem decode_seedB_2 :
    CFSG.Blueprint.NativeSporadic.decode 3 21 1 CFSG.Sporadic.McL.Native.seedB = decR bR := by
  decide +kernel

private theorem codes_targets_3 : (codes ()).getD 77 oneR = xLit ∧
    (codes ()).getD 85 oneR = yLit ∧ (codes ()).getD 103 oneR = zLit ∧
    (codes ()).getD 108 oneR = wLit ∧ (codes ()).getD 87 oneR = iLit ∧
    (codes ()).getD 90 oneR = jLit := by
  decide +kernel

private theorem cubes_4 : mulR (mulR xLit xLit) xLit = oneR ∧
    mulR (mulR yLit yLit) yLit = oneR ∧ mulR (mulR zLit zLit) zLit = oneR ∧
    mulR (mulR wLit wLit) wLit = oneR := by
  decide +kernel

private theorem comms_5 : mulR yLit xLit = mulR xLit yLit ∧ mulR zLit xLit = mulR xLit zLit ∧
    mulR zLit yLit = mulR yLit zLit ∧ mulR wLit xLit = mulR xLit wLit ∧
    mulR wLit yLit = mulR yLit wLit ∧ mulR wLit zLit = mulR zLit wLit := by
  decide +kernel

private theorem q8_rels_6 : mulR (mulR (mulR iLit iLit) iLit) iLit = oneR ∧
    mulR (mulR (mulR jLit jLit) jLit) jLit = oneR ∧
    mulR jLit iLit = mulR (mulR (mulR iLit iLit) iLit) jLit := by
  decide +kernel

private theorem x_rels_7 : mulR xLit iLit = mulR jLit xLit ∧
    mulR xLit jLit = mulR (mulR (mulR (mulR iLit iLit) iLit) jLit) xLit := by
  decide +kernel

private theorem y_rels_8 : mulR yLit iLit = mulR iLit yLit ∧
    mulR yLit jLit = mulR jLit yLit := by
  decide +kernel

private theorem xi_entries_9 : entR (mulR xLit iLit) 0 0 = 2 ∧ entR (mulR iLit xLit) 0 0 = 1 := by
  decide +kernel

private theorem x_entry_10 : entR xLit 0 0 = 2 := by
  decide +kernel

private theorem fixes_11 : mulR xLit (colR v1L) = colR v1L ∧ mulR xLit (colR v2L) = colR v2L ∧
    mulR yLit (colR v2L) = colR v2L ∧ mulR xLit (colR v3L) = colR v3L ∧
    mulR yLit (colR v3L) = colR v3L ∧ mulR zLit (colR v3L) = colR v3L := by
  decide +kernel

private theorem moves_12 :
    (entR (mulR yLit (colR v1L)) 1 0 = 1 ∧ entR (colR v1L) 1 0 = 2) ∧
    (entR (mulR zLit (colR v2L)) 0 0 = 0 ∧ entR (colR v2L) 0 0 = 2) ∧
    (entR (mulR wLit (colR v3L)) 0 0 = 1 ∧ entR (colR v3L) 0 0 = 2) := by
  decide +kernel

end CertificateChecks.Batch8175

namespace Certificates

open CertificateChecks

open CFSG.RankThree.PartTwo.Sec4.Res417Five.McLE81 in
theorem certificate8175 : decR oneR = 1 ∧
    CFSG.Blueprint.NativeSporadic.decode 3 21 1 CFSG.Sporadic.McL.Native.seedA = decR aR ∧
    CFSG.Blueprint.NativeSporadic.decode 3 21 1 CFSG.Sporadic.McL.Native.seedB = decR bR ∧
    ((codes ()).getD 77 oneR = xLit ∧ (codes ()).getD 85 oneR = yLit ∧
      (codes ()).getD 103 oneR = zLit ∧ (codes ()).getD 108 oneR = wLit ∧
      (codes ()).getD 87 oneR = iLit ∧ (codes ()).getD 90 oneR = jLit) ∧
    (mulR (mulR xLit xLit) xLit = oneR ∧ mulR (mulR yLit yLit) yLit = oneR ∧
      mulR (mulR zLit zLit) zLit = oneR ∧ mulR (mulR wLit wLit) wLit = oneR) ∧
    (mulR yLit xLit = mulR xLit yLit ∧ mulR zLit xLit = mulR xLit zLit ∧
      mulR zLit yLit = mulR yLit zLit ∧ mulR wLit xLit = mulR xLit wLit ∧
      mulR wLit yLit = mulR yLit wLit ∧ mulR wLit zLit = mulR zLit wLit) ∧
    (mulR (mulR (mulR iLit iLit) iLit) iLit = oneR ∧
      mulR (mulR (mulR jLit jLit) jLit) jLit = oneR ∧
      mulR jLit iLit = mulR (mulR (mulR iLit iLit) iLit) jLit) ∧
    (mulR xLit iLit = mulR jLit xLit ∧
      mulR xLit jLit = mulR (mulR (mulR (mulR iLit iLit) iLit) jLit) xLit) ∧
    (mulR yLit iLit = mulR iLit yLit ∧ mulR yLit jLit = mulR jLit yLit) ∧
    (entR (mulR xLit iLit) 0 0 = 2 ∧ entR (mulR iLit xLit) 0 0 = 1) ∧
    entR xLit 0 0 = 2 ∧
    (mulR xLit (colR v1L) = colR v1L ∧ mulR xLit (colR v2L) = colR v2L ∧
      mulR yLit (colR v2L) = colR v2L ∧ mulR xLit (colR v3L) = colR v3L ∧
      mulR yLit (colR v3L) = colR v3L ∧ mulR zLit (colR v3L) = colR v3L) ∧
    ((entR (mulR yLit (colR v1L)) 1 0 = 1 ∧ entR (colR v1L) 1 0 = 2) ∧
      (entR (mulR zLit (colR v2L)) 0 0 = 0 ∧ entR (colR v2L) 0 0 = 2) ∧
      (entR (mulR wLit (colR v3L)) 0 0 = 1 ∧ entR (colR v3L) 0 0 = 2)) := by
  exact ⟨CertificateChecks.Batch8175.decR_oneR_0, CertificateChecks.Batch8175.decode_seedA_1, CertificateChecks.Batch8175.decode_seedB_2,
    CertificateChecks.Batch8175.codes_targets_3, CertificateChecks.Batch8175.cubes_4, CertificateChecks.Batch8175.comms_5, CertificateChecks.Batch8175.q8_rels_6,
    CertificateChecks.Batch8175.x_rels_7, CertificateChecks.Batch8175.y_rels_8, CertificateChecks.Batch8175.xi_entries_9, CertificateChecks.Batch8175.x_entry_10,
    CertificateChecks.Batch8175.fixes_11, CertificateChecks.Batch8175.moves_12⟩

end Certificates

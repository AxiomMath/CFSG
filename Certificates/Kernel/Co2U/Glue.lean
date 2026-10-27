module

public import Certificates.Kernel.Co2U.Check
public import CFSG.Certificates.Kernel.Co2U.TwinSound
public import Certificates.Kernel.Co2W11.Glue

public section

namespace CertificateChecks.KernelCo2U

open CFSG.KC.Co2U CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.KC.F2TriSep CFSG.KC.M1F2
  CFSG.GF2W1112 CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelLC.Co2Ops
  CertificateChecks.KernelCo2W11

theorem wordRows_eq (w : List Bool) : w12WordRows (w12Co2RowsA ()) (w12Co2RowsB ()) w =
    unpackR 22 (wordB 22 SA.M SB.M w (idF 22)) := by
  rw [unpack_wordB, CFSG.KC.VecK.unpackR_idF]
  rfl

theorem rows_eq : w12URows () = (EltP.P.map (unpackR 22)).toArray := by
  have hw := wordsK_map SA.M SB.M W.chars EltP.P ch38957w_
  have e1 : w12URows () = w12UWords.map fun s =>
      w12WordRows (w12Co2RowsA ()) (w12Co2RowsB ()) (w12UParse s) := by
    rw [w12URows]
  rw [e1, W.eq, List.map_toArray, List.map_map, ← hw]
  refine congrArg List.toArray (List.map_congr_left ?_)
  intro c _
  rw [Function.comp_apply, w12UParse, String.toList_ofList, wordRows_eq]

theorem getElem_rows {P : List Nat} (hP : P.length = 33) :
    ∀ i < 33, (P.map (unpackR 22)).toArray[i]! = unpackR 22 (nthK P i) := by
  intro i hi
  have hi' : i < P.length := by rw [hP]; exact hi
  rw [nthK_eq, getElem!_pos _ i (by simpa using hi'), List.getElem_toArray, List.getElem_map,
    List.getD_eq_getElem _ _ hi']

theorem check1 : w12UCheck1 () = true := by
  have hG := getElem_rows ch38957len_
  rw [w12UCheck1]
  simp only [rows_eq]
  rw [eqCheck_eq hG, ch38957a_, Bool.true_and, hG 0 (by decide), idRows_eq, w12UEqR_unpack,
    nthK_eq, ch38957e_]
  rfl

theorem check2 : w12UCheck2 () = true := by
  rw [w12UCheck2, rows_eq, eqCheck_eq (getElem_rows ch38957len_), ch38958a_]

end CertificateChecks.KernelCo2U

end

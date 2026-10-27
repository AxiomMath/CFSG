
module

public import Certificates.Kernel.Co1M.W10071
public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1Cover.Bridge
public import CFSG.Certificates.Kernel.Co1M.FixListSound
public import CFSG.Certificates.Kernel.Co1BTrSound
public import CFSG.Sporadic.Co1.Module.LeechOddChecksInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KC.Co1Fix CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KLie.CT CFSG.KC.VecK
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Odd CertificateChecks.KernelCo1Cover

theorem c71_progL : PROG71 = prog := eq_of_beq (by quickRfl)

theorem c71_regs : regsRows = (cmRP71.map (unpackR 24)).toArray := by
  rw [regsRows, initRows, rowsA_eq, rowsB_eq, ← c71_progL, ← prog_sound cm71_prog_chk]
  rfl

theorem c71_getL (x : Nat) : ∀ (L : List Nat) (i : Nat), getL x L i = L.getD i x
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => c71_getL x L i

theorem c71_rr {i : Nat} (hi : i < cmRP71.length) : rr i = unpackR 24 (getL 0 cmRP71 i) := by
  rw [rr, c71_regs, c71_getL, List.getD_eq_getElem _ _ hi]
  simp [hi]

theorem c71_len : cmRP71.length = 94 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem c71_Wk {k s : Nat} (hs : sIdx[k]! = s) (hsl : s < 94) {W : List Nat}
    (h : fixListK (trK 24 (getL 0 cmRP71 27)) (trK 24 (getL 0 cmRP71 s)) FR3 W = true) : Wk k = W := by
  rw [Wk, hs, c71_rr (by rw [c71_len]; norm_num), c71_rr (by rw [c71_len]; exact hsl)]
  simp only [List.map_cons, List.map_nil, CFSG.KC.F2W.transposeRows_unpackR]
  exact fixList_eq_of w71_fix h

theorem c71_W1 : vecsOne = W1L := c71_Wk (k := 1) (by decide) (by norm_num) w71_one

theorem c71_W2 : vecsTwo = W2L := c71_Wk (k := 2) (by decide) (by norm_num) w71_two

theorem c71_isT2 (x : Nat) : isT2 x = orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 x :=
  cm_orb_inPts x

theorem c71_isT4 (x : Nat) : isT4' x = (x != 0 && !q0N (transposeRows 24 qRows) x &&
    !orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 x) := by
  unfold isT4' type4N
  rw [← c71_isT2]
  rfl

theorem c71_isT2f : isT2 = fun x => orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 x :=
  funext c71_isT2

theorem c71_isT4f : isT4' = fun x => (x != 0 && !q0N (transposeRows 24 qRows) x &&
    !orbMemK 98280 (lk CertificateChecks.KernelVec.Co1.S 32) 17 x) :=
  funext c71_isT4

theorem c71_noTwo : noTwoOK = true := by
  unfold noTwoOK
  rw [c71_W1]
  simp only [c71_isT2]
  quickRfl

theorem c71_cover : coverOK = true := by
  unfold coverOK w2List f4List
  rw [c71_W2, c71_isT2f, c71_isT4f]
  quickRfl

theorem c71_triple : tripleOK = true := by
  unfold tripleOK w2List
  rw [c71_W2, c71_isT2f, c71_isT4f]
  quickRfl

end CertificateChecks.KernelCo1M

end

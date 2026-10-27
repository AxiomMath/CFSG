module

public import CFSG.Timmesfeld.Moufang.J2Mat
public import CFSG.Timmesfeld.Moufang.LinePres

public section

namespace CFSG.Timmesfeld.Moufang.J2

open CFSG.Sporadic.Bridge.J2 (natX natXi idL wfM mulL lwordL mA mB)

theorem genL_wf_0 : wfM (genL 0) = true := by
  decide +kernel

theorem genL_wf_1 : wfM (genL 1) = true := by
  decide +kernel

theorem genL_wf_2 : wfM (genL 2) = true := by
  decide +kernel

theorem genL_wf_3 : wfM (genL 3) = true := by
  decide +kernel

theorem genL_wf_4 : wfM (genL 4) = true := by
  decide +kernel

theorem genL_wf_5 : wfM (genL 5) = true := by
  decide +kernel

theorem genL_wf_6 : wfM (genL 6) = true := by
  decide +kernel

theorem genL_sq_0 : mulL (genL 0) (genL 0) = idL := by
  decide +kernel

theorem genL_sq_1 : mulL (genL 1) (genL 1) = idL := by
  decide +kernel

theorem genL_sq_2 : mulL (genL 2) (genL 2) = idL := by
  decide +kernel

theorem genL_sq_3 : mulL (genL 3) (genL 3) = idL := by
  decide +kernel

theorem genL_sq_4 : mulL (genL 4) (genL 4) = idL := by
  decide +kernel

theorem genL_sq_5 : mulL (genL 5) (genL 5) = idL := by
  decide +kernel

theorem genL_sq_6 : mulL (genL 6) (genL 6) = idL := by
  decide +kernel

theorem mulL_idL_idL : mulL idL idL = idL := by
  decide +kernel

theorem lwordL_wordD : lwordL natX natXi wordD idL = genL 0 := by
  decide +kernel

theorem lwordL_genWord_1 : lwordL letterABD letterABDInv (genWord 1) idL = genL 1 := by
  decide +kernel

theorem lwordL_genWord_2 : lwordL letterABD letterABDInv (genWord 2) idL = genL 2 := by
  decide +kernel

theorem lwordL_genWord_3 : lwordL letterABD letterABDInv (genWord 3) idL = genL 3 := by
  decide +kernel

theorem lwordL_genWord_4 : lwordL letterABD letterABDInv (genWord 4) idL = genL 4 := by
  decide +kernel

theorem lwordL_genWord_5 : lwordL letterABD letterABDInv (genWord 5) idL = genL 5 := by
  decide +kernel

theorem lwordL_genWord_6 : lwordL letterABD letterABDInv (genWord 6) idL = genL 6 := by
  decide +kernel

@[expose] def relL (k : ℕ) : List (ℕ × Bool) :=
  ((lineRels 5 true).getD k []).map fun l => (l.1.val, l.2)

theorem length_lineRels : (lineRels 5 true).length = 34 := by
  decide +kernel

theorem relL_0 : lwordL genL genL (relL 0) idL = idL := by
  decide +kernel

theorem relL_1 : lwordL genL genL (relL 1) idL = idL := by
  decide +kernel

theorem relL_2 : lwordL genL genL (relL 2) idL = idL := by
  decide +kernel

theorem relL_3 : lwordL genL genL (relL 3) idL = idL := by
  decide +kernel

theorem relL_4 : lwordL genL genL (relL 4) idL = idL := by
  decide +kernel

theorem relL_5 : lwordL genL genL (relL 5) idL = idL := by
  decide +kernel

theorem relL_6 : lwordL genL genL (relL 6) idL = idL := by
  decide +kernel

theorem relL_7 : lwordL genL genL (relL 7) idL = idL := by
  decide +kernel

theorem relL_8 : lwordL genL genL (relL 8) idL = idL := by
  decide +kernel

theorem relL_9 : lwordL genL genL (relL 9) idL = idL := by
  decide +kernel

theorem relL_10 : lwordL genL genL (relL 10) idL = idL := by
  decide +kernel

theorem relL_11 : lwordL genL genL (relL 11) idL = idL := by
  decide +kernel

theorem relL_12 : lwordL genL genL (relL 12) idL = idL := by
  decide +kernel

theorem relL_13 : lwordL genL genL (relL 13) idL = idL := by
  decide +kernel

theorem relL_14 : lwordL genL genL (relL 14) idL = idL := by
  decide +kernel

theorem relL_15 : lwordL genL genL (relL 15) idL = idL := by
  decide +kernel

theorem relL_16 : lwordL genL genL (relL 16) idL = idL := by
  decide +kernel

theorem relL_17 : lwordL genL genL (relL 17) idL = idL := by
  decide +kernel

theorem relL_18 : lwordL genL genL (relL 18) idL = idL := by
  decide +kernel

theorem relL_19 : lwordL genL genL (relL 19) idL = idL := by
  decide +kernel

theorem relL_20 : lwordL genL genL (relL 20) idL = idL := by
  decide +kernel

theorem relL_21 : lwordL genL genL (relL 21) idL = idL := by
  decide +kernel

theorem relL_22 : lwordL genL genL (relL 22) idL = idL := by
  decide +kernel

theorem relL_23 : lwordL genL genL (relL 23) idL = idL := by
  decide +kernel

theorem relL_24 : lwordL genL genL (relL 24) idL = idL := by
  decide +kernel

theorem relL_25 : lwordL genL genL (relL 25) idL = idL := by
  decide +kernel

theorem relL_26 : lwordL genL genL (relL 26) idL = idL := by
  decide +kernel

theorem relL_27 : lwordL genL genL (relL 27) idL = idL := by
  decide +kernel

theorem relL_28 : lwordL genL genL (relL 28) idL = idL := by
  decide +kernel

theorem relL_29 : lwordL genL genL (relL 29) idL = idL := by
  decide +kernel

theorem relL_30 : lwordL genL genL (relL 30) idL = idL := by
  decide +kernel

theorem relL_31 : lwordL genL genL (relL 31) idL = idL := by
  decide +kernel

theorem relL_32 : lwordL genL genL (relL 32) idL = idL := by
  decide +kernel

theorem relL_33 : lwordL genL genL (relL 33) idL = idL := by
  decide +kernel

theorem lwordL_wordA : lwordL genL genL (wordA.map fun l => (l.1.val, l.2)) idL = mA := by
  decide +kernel

theorem lwordL_wordB : lwordL genL genL (wordB.map fun l => (l.1.val, l.2)) idL = mB := by
  decide +kernel

end CFSG.Timmesfeld.Moufang.J2

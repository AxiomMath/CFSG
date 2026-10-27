module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawE7Data

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw.Check

open CFSG.Decide CFSG.Decide.F3

theorem run_mode4 : run 4 form4 ls4 certs4 = true := by decide +kernel

theorem boundOK_mode4 : boundOK (pdim 4) (ptabF 4) (ptabH 4) = true := by decide +kernel

theorem e6Masks4_eq : e6Masks4 = e6Lines4.map (zmask 4) := by decide +kernel

theorem repMasks4_eq : repMasks4 = (repVecs (dim 4)).map (zmask 4) := by decide +kernel

theorem bitCount_e6Masks4 : ∀ z ∈ e6Masks4, bitCount (nroots 4) z = 36 := by decide +kernel

set_option maxHeartbeats 0 in
theorem planeOK4_e6Masks4 : ∀ z ∈ e6Masks4, ∀ z' ∈ repMasks4, planeOK4 (z &&& z') = true := by
  decide +kernel

end CFSG.StandardType.GGQ2Frame.ExcRaw.Check

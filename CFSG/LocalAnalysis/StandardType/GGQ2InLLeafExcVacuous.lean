module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLCoverFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafExcData
public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafExcRun

public section

namespace CFSG.StandardType.GGQ2Frame

namespace ExcRaw

open CFSG.Decide.F3 Check

theorem run_mode0 : run 0 form0 (repVecs (dim 0)) certs0 = true := by decide +kernel
theorem run_mode1 : run 1 form1 (repVecs (dim 1)) certs1 = true := by decide +kernel
theorem run_mode2 : run 2 form2 (repVecs (dim 2)) certs2 = true := by decide +kernel
theorem run_mode3 : run 3 form3 (repVecs (dim 3)) certs3 = true := by decide +kernel
theorem run_mode5 : run 5 form5 (repVecs (dim 5)) certs5 = true := by decide +kernel

theorem boundOK_mode0 : boundOK (pdim 0) (ptabF 0) (ptabH 0) = true := by decide +kernel
theorem boundOK_mode1 : boundOK (pdim 1) (ptabF 1) (ptabH 1) = true := by decide +kernel
theorem boundOK_mode2 : boundOK (pdim 2) (ptabF 2) (ptabH 2) = true := by decide +kernel
theorem boundOK_mode3 : boundOK (pdim 3) (ptabF 3) (ptabH 3) = true := by decide +kernel
theorem boundOK_mode5 : boundOK (pdim 5) (ptabF 5) (ptabH 5) = true := by decide +kernel

theorem noInternalAt_excRaw (m : Fin 6) (hm : m ≠ 4) {v : V m} (hv : v ≠ 0) :
    NoInternalAt m v := by
  revert v hv
  fin_cases m
  · intro v hv
    exact noInternalAt_of_run_repVecs (natAbs_pairing_le boundOK_mode0) run_mode0 hv
  · intro v hv
    exact noInternalAt_of_run_repVecs (natAbs_pairing_le boundOK_mode1) run_mode1 hv
  · intro v hv
    exact noInternalAt_of_run_repVecs (natAbs_pairing_le boundOK_mode2) run_mode2 hv
  · intro v hv
    exact noInternalAt_of_run_repVecs (natAbs_pairing_le boundOK_mode3) run_mode3 hv
  · intro v hv
    exact absurd rfl hm
  · intro v hv
    exact noInternalAt_of_run_repVecs (natAbs_pairing_le boundOK_mode5) run_mode5 hv

end ExcRaw

theorem inLLeafCases_excRaw (m : Fin 6) (hm : m ≠ 4) : InLLeafCases (excRaw m) := by
  intro vx hvx ℓ _ _ hocc hcent hin
  exact (ExcRaw.noInternalAt_excRaw m hm hvx ℓ hocc hcent hin).elim

end CFSG.StandardType.GGQ2Frame

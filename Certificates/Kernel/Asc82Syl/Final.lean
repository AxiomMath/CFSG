module

public import CFSG.Certificates.Kernel.Asc82Syl.Group
public import Certificates.Kernel.Asc82Syl.Checks

public section

namespace CFSG.KS.Asc82Syl

open CFSG.KD.Asc82Syl CFSG.KS.Mat3 CFSG.KC.Ord CFSG.OddStandard.SmallF3.Omega

theorem a82_matDP (i j : Fin 6) : mat dP i j = Matrix.diagonal ffRADPlus i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem a82_matDM (i j : Fin 6) : mat dM i j = Matrix.diagonal ffRADMinus i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem a82_validDP : valid3 36 LO dP = true := by decide +kernel

theorem a82_validDM : valid3 36 LO dM = true := by decide +kernel

theorem a82_lenP : gP.length = 5 + 4 := by decide +kernel

theorem a82_lenM : gM.length = 6 + 4 := by decide +kernel

theorem a82_groupP : FFRAGroup 512 ffRADPlus false 32 :=
  side_group (k := 5) (funext fun i => funext fun j => a82_matDP i j)
    (fun i => by fin_cases i <;> decide) (by omega) a82_lenP rfl rfl ch442274_consts
    (valid_iff.1 a82_validDP) ch442274_genP ch442274_enumP ch442274_keyP ch442274_relP
    ch442274_qtP ch442274_ctP ch442274_omP ch442274_famP

theorem a82_groupM : FFRAGroup 1024 ffRADMinus true 32 :=
  side_group (k := 6) (funext fun i => funext fun j => a82_matDM i j)
    (fun i => by fin_cases i <;> decide) (by omega) a82_lenM rfl rfl ch442274_consts
    (valid_iff.1 a82_validDM) ch442274_genM ch442274_enumM ch442274_keyM ch442274_relM
    ch442274_qtM ch442274_ctM ch442274_omM ch442274_famM

end CFSG.KS.Asc82Syl

end

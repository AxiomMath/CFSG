module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieF
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieE

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.Sec53F.Unit

section Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem unStdV_Y (hf : 2 ≤ f) :
    UnStdV (hypPSU h 2 1) (hypProjUnitriangular h 2 1) (u5PtP h) (u5LnP h) (z5Y h) (t5Y h)
      (v5Y h) where
  V4_le := v5Y_le_U
  V4_ab _ ha _ hb := v5Y_comm ha hb
  V4_sq _ ha := v5Y_sq ha
  V4_zt := ⟨z5Y_mem_v5Y, t5Y_mem_v5Y⟩
  V4_eq := v5Y_eq_centerOf_pCoreOf
  V4_unique _ hE hab hsq hcard := V4_unique_Y hE hab hsq hcard
  z_ZP := z5Y_mem_centerOf hf
  ZP_trans _ hx hx1 := ZP_trans_Y hf hx hx1
  cz := cent_z_Y
  ct := cent_t_Y
  nz := nz_Y
  nt := nt_Y

end Hyp

end CFSG.Quasithin.H13.F431.Un

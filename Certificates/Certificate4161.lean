module

public import Certificates.Data.U42F431Check

public section

open U42F431

namespace Certificates

private theorem chkTau_true : chkTau = true := by decide +kernel
private theorem chkLines_true : chkLines = true := by decide +kernel
private theorem chkP_true : chkP = true := by decide +kernel
private theorem chkT_true : chkT = true := by decide +kernel
private theorem chkInv_true : chkInv = true := by decide +kernel
private theorem chkLat_true : chkLat = true := by decide +kernel
private theorem chkAg_true : chkAg = true := by decide +kernel
private theorem chkMisc_true : chkMisc = true := by decide +kernel
private theorem chkLit_true : chkLit = true := by decide +kernel

open U42F431 in
theorem certificate4161 : chkTau = true ∧ chkLines = true ∧ chkP = true ∧ chkT = true ∧ chkInv = true ∧
    chkLat = true ∧ chkAg = true ∧ chkMisc = true ∧ chkLit = true :=
  ⟨chkTau_true, chkLines_true, chkP_true, chkT_true, chkInv_true, chkLat_true, chkAg_true,
    chkMisc_true, chkLit_true⟩

end Certificates

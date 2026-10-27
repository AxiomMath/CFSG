module

public import Certificates.Data.U42F45Check

public section

open U42F431

namespace Certificates

private theorem chkF45Lay_true : chkF45Lay = true := by decide +kernel
private theorem chkF45Pt_true : chkF45Pt = true := by decide +kernel
private theorem chkF45Ln_true : chkF45Ln = true := by decide +kernel

open U42F431 in
theorem certificate4162 : chkF45Lay = true ∧ chkF45Pt = true ∧ chkF45Ln = true :=
  ⟨chkF45Lay_true, chkF45Pt_true, chkF45Ln_true⟩

end Certificates

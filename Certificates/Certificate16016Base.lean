
module

public import CFSG.Monster.B.TwoA.Unitary.ActionInputs
public import Certificates.Certificate3026

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary
  CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice CFSG.Monster.B.Short
  CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Census

public section


open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary
  CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice CFSG.Monster.B.Short
  CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch16016

private theorem permRowOK_eq_0 : ∀ k < 6, permRowOK k = true := by
  decide +kernel

private theorem permQuotOK_eq_1 : ∀ k < 6, permQuotOK k = true := by
  decide +kernel

private theorem wordRowsOK_eq_2 : ∀ k < 11, wordRowsOK k = true := by
  decide +kernel

end CertificateChecks.Batch16016

namespace Certificates

end Certificates


module

public import Certificates.Certificate16016Base
import all Certificates.Certificate16016Base


public section

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

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary
  CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice CFSG.Monster.B.Short
  CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Census

end CertificateChecks.Batch16016

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary
  CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice CFSG.Monster.B.Short
  CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Census in
theorem certificate16016 : (
    ∀ k < 6, permRowOK k = true
  ) ∧ (
    ∀ k < 6, permQuotOK k = true
  ) ∧ (
    ∀ k < 11, wordRowsOK k = true
  ) := by
  exact ⟨CertificateChecks.Batch16016.permRowOK_eq_0, CertificateChecks.Batch16016.permQuotOK_eq_1, CertificateChecks.Batch16016.wordRowsOK_eq_2⟩

end Certificates

module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.TwoA.Census.SymTrace
public import CFSG.Monster.Existence.ELevelConv
public import CFSG.Monster.VisQuot.Monomial
public import Certificates.Certificate8955

public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch16006

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

private theorem eb_deltaPair_zero_one_0 : Model.dualN 3 = 191 := by
  decide +kernel

private theorem eb_deltaPair_zero_two_1 : Model.dualN 5 = 127 := by
  decide +kernel

end CertificateChecks.Batch16006

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census in
theorem certificate16006 : (
    Model.dualN 3 = 191
  ) ∧ (
    Model.dualN 5 = 127
  ) := by
  exact ⟨CertificateChecks.Batch16006.eb_deltaPair_zero_one_0, CertificateChecks.Batch16006.eb_deltaPair_zero_two_1⟩

end Certificates

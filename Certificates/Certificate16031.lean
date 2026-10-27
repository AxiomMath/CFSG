module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.TwoA.Census.CosetSquares
public import CFSG.Monster.Existence.TwoPoint.LeechForm

public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch16031

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

private theorem alphaOne_pauli_zero_zero_four_0 :
    alphaN 1 (false, 0, 4) = (false, 3, 56) := by
  decide +kernel

private theorem mul_alphaOne_qP_zero_zero_four_1 :
    Model.Pauli.mul (false, 0, 4) (false, 3, 56) = (false, 3, 60) := by
  decide +kernel

end CertificateChecks.Batch16031

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census in
theorem certificate16031 : (
    alphaN 1 (false, 0, 4) = (false, 3, 56)
  ) ∧ (
    Model.Pauli.mul (false, 0, 4) (false, 3, 56) = (false, 3, 60)
  ) := by
  exact ⟨CertificateChecks.Batch16031.alphaOne_pauli_zero_zero_four_0, CertificateChecks.Batch16031.mul_alphaOne_qP_zero_zero_four_1⟩

end Certificates

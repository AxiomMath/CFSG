module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.TwoA.Census.CosetSquares
public import CFSG.Monster.Existence.ELevelConv

public section

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch16019

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census

private theorem alphaN_one_63_0 : alphaN 1 (false, 63, 0) = (false, 63, 0) := by
  decide +kernel

private theorem alphaN_one_60_48_1 : alphaN 1 (false, 60, 48) = (false, 60, 48) := by
  decide +kernel

end CertificateChecks.Batch16019

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Code CFSG.Monster.Spin
  CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Short CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.Monster.VisCert
  CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.TwoA.Census in
theorem certificate16019 : (
    alphaN 1 (false, 63, 0) = (false, 63, 0)
  ) ∧ (
    alphaN 1 (false, 60, 48) = (false, 60, 48)
  ) := by
  exact ⟨CertificateChecks.Batch16019.alphaN_one_63_0, CertificateChecks.Batch16019.alphaN_one_60_48_1⟩

end Certificates

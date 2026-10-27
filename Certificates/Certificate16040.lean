module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.Co2.BFS
public import CFSG.Monster.B.Short.Rootless
public import CFSG.Monster.B.TwoA.Unitary.NData
public import Certificates.Certificate3062

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary
  CFSG.Monster.B.Short CFSG.Monster.B.Co2

public section


open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary
  CFSG.Monster.B.Short CFSG.Monster.B.Co2

namespace CertificateChecks.Batch16040

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary
  CFSG.Monster.B.Short CFSG.Monster.B.Co2

private theorem n6Vec_one_three_0 : n6VecArr[1]! = 12319 ∧ n6VecArr[3]! = 12288 := by
  decide +kernel

end CertificateChecks.Batch16040

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 in
theorem certificate16040 : n6VecArr[1]! = 12319 ∧ n6VecArr[3]! = 12288 := by
  exact CertificateChecks.Batch16040.n6Vec_one_three_0

end Certificates

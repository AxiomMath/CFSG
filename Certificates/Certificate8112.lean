module

public import CFSG.RankThree.Co2.FuseCounts
import Certificates.Kernel.Co2Fuse.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.RankThree.Co2 in
theorem certificate8112 : fuseN {0, 2, 7} {4, 6, 8} {9} = 32 ∧ fuseN {0, 2, 7} {9} {4, 6, 8} = 0 ∧
    fuseN {0, 2, 7} {4, 6, 8} {1, 3, 5, 9} = 68 ∧ fuseN {0, 2, 7} {1, 3, 5, 9} {4, 6, 8} = 36 :=
  KernelSpor.Co2Fuse.fuse_counts_final

end Certificates

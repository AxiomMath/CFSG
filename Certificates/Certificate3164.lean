module

public import CFSG.Sporadic.Schreier.M22Data
import Certificates.Kernel.Sporadic.M22Pair5Bridge
public import CFSG.Sporadic.Schreier.ImagePairs

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu in
theorem certificate3164 : (ordW 22 [toTable m22gA, toTable m22gB, toTable m22gB] 5 = true)
    ∧ (pairCount (orderTables m22Certificate 2) (orderTables m22Certificate 4)
       (fun x y => pairTest 22 11 6 2 4 x y && ordW 22 [x, y, y] 5) = 887040) := KernelSpor.M22Pair5.counts

end Certificates

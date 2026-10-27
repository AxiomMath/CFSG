
module

public import Certificates.Certificate2168Base

public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
import Certificates.Kernel.SporSch.J4S.KsP

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier in
theorem certificate2168 : (rootCheck = true)
    ∧ (colsCheck = true)
    ∧ (elemCheck = true)
    ∧ (O.vmul ksetVectors[0]! Zn.1 < 2 ^ 112)
    ∧ (∀ i < ksetSize, ksetVectors[i]! < 2 ^ 112 ∧ (ksetEdges[i]!)[0]! < ksetSize ∧
      ksetVectors[(ksetEdges[i]!)[0]!]! = O.vmul ksetVectors[i]! Xn.1 ∧
      (ksetEdges[i]!)[1]! < ksetSize ∧
      ksetVectors[(ksetEdges[i]!)[1]!]! = O.vmul ksetVectors[i]! Yn.1 ∧
      ksetVectors[i]! ≠ O.vmul ksetVectors[0]! Zn.1
    )
    ∧ (CFSG.Sporadic.J4.Native.matChecks = true)
    ∧ (comp11 xColumns xInvColumns = CFSG.Sporadic.SmallF2.Native.idRows 11)
    ∧ (comp11 yColumns yInvColumns = CFSG.Sporadic.SmallF2.Native.idRows 11) := KernelSporSch.J4KsP.facts

end Certificates

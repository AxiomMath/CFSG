
module

public import CFSG.Sporadic.Schreier.Co1FullOrbCheckInputs
public import CFSG.Sporadic.Schreier.Co1OrbEnum
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import CFSG.Sporadic.Schreier.Co1XSet
import Certificates.Kernel.SporSch.Co1.Full2135Base
import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheck
meta import CFSG.Sporadic.Schreier.Co1ElemData
meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
meta import Certificates.Data.CFSGNative.Co1Schreier.Base
meta import Certificates.Data.CFSGNative.Co1.Data
import CFSG.Sporadic.Schreier.Co1StabCheckInputs
meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
meta import CFSG.Sporadic.Schreier.Co1StabData
meta import CFSG.Sporadic.Schreier.Co1FullOrbCheckBase
meta import Certificates.Data.CFSGNative.HS.SmallF2
meta import Certificates.Data.CFSGNative.Th.Tables
meta import Certificates.Data.CFSGNative.Th.Orbit
import Certificates.Data.CFSGNative.Co1.Data

@[expose] public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co1Schreier in
theorem orbit_two_facts :
    kOrbit GA (CFSG.Sporadic.SmallF2.toVecD 24 2) = co1X ∧
      ∀ i < 98280, (Native.fullOrb 2).pts[i]! < 2 ^ 24 :=
  ⟨KernelSporSch.Co1Full2135.X_eq.trans co1X_eq_enumSet.symm,
    fun _ hi => KernelSporSch.Co1Full2135.pts_lt hi⟩

end Certificates

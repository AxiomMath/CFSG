
module

public import Certificates.Certificate2135Base

public import CFSG.Sporadic.Schreier.Co1FullOrbCheckInputs
public import CFSG.Sporadic.Schreier.Co1OrbEnum
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import CFSG.Sporadic.Schreier.Co1XSet
import Certificates.Kernel.SporSch.Co1.Full2135
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

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier in
theorem certificate2135 : (kOrbit CFSG.Sporadic.Co1Schreier.GA (CFSG.Sporadic.SmallF2.toVecD 24 2) = co1X ∧
      ∀ i < 98280, (Native.fullOrb 2).pts[i]! < 2 ^ 24) ∧
    (∀ v : Vec24, ∃ k < 4, v ∈ kOrbit CFSG.Sporadic.Co1Schreier.GA (CFSG.Sporadic.SmallF2.toVecD 24 (Native.fullRoot k))) ∧
    (∀ k < 4, (kOrbit CFSG.Sporadic.Co1Schreier.GA (CFSG.Sporadic.SmallF2.toVecD 24 (Native.fullRoot k))).ncard =
      Native.fullSize k) ∧
    (∀ k < 4, ∀ c < 2 ^ 24,
      CFSG.Sporadic.SmallF2.toVecD 24 c ∈ kOrbit CFSG.Sporadic.Co1Schreier.GA (CFSG.Sporadic.SmallF2.toVecD 24 (Native.fullRoot k)) →
        Native.fullRoot k ≤ c) :=
  ⟨orbit_two_facts, KernelSporSch.Co1Full2135.facts⟩

end Certificates

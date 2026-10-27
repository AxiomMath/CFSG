
module

public import CFSG.Sporadic.Schreier.Co1FullOrbCheckBase

public import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public import Certificates.Data.CFSGNative.Co1.Data
public meta import CFSG.Sporadic.Schreier.Co1OrbEnumCheck
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.Th.Tables
public meta import Certificates.Data.CFSGNative.Th.Orbit
public import CFSG.Sporadic.Schreier.Co1FullOrbCheckInputs
public import Certificates.Certificate2135

public section

namespace CFSG.Sporadic.Co1Schreier

theorem full_orbit_two :
    kOrbit GA (CFSG.Sporadic.SmallF2.toVecD 24 2) = co1X :=
  Certificates.certificate2135.1.1

theorem fullOrb_two_lt {i : ℕ} (hi : i < 98280) :
    (Native.fullOrb 2).pts[i]! < 2 ^ 24 :=
  Certificates.certificate2135.1.2 i hi

theorem full_orbits_cover (v : Vec24) :
    ∃ k < 4, v ∈ kOrbit GA (CFSG.Sporadic.SmallF2.toVecD 24 (Native.fullRoot k)) :=
  Certificates.certificate2135.2.1 v

theorem full_orbits_ncard {k : ℕ} (hk : k < 4) :
    (kOrbit GA (CFSG.Sporadic.SmallF2.toVecD 24 (Native.fullRoot k))).ncard = Native.fullSize k :=
  Certificates.certificate2135.2.2.1 k hk

theorem full_orbits_least {k : ℕ} (hk : k < 4) {c : ℕ}
    (hc : c < 2 ^ 24)
    (h : CFSG.Sporadic.SmallF2.toVecD 24 c ∈
      kOrbit GA (CFSG.Sporadic.SmallF2.toVecD 24 (Native.fullRoot k))) :
    Native.fullRoot k ≤ c :=
  Certificates.certificate2135.2.2.2 k hk c hc h

end CFSG.Sporadic.Co1Schreier

module

public import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Sporadic.FischerOddCore.Fi22SylowCheckInputs
public import Certificates.Certificate2072

public section

namespace CFSG.Sporadic.FischerOddCore

theorem fi22Syl_facts {s : ℕ} (hs : s < 11) :
    fi22CentSylowSub s ≤ fi22H (fi22CentSylowField s 0) ∧
    Nat.card (fi22CentSylowSub s) = fi22CentSylowField s 2 ∧
    (∀ g ∈ fi22CentSylowSub s, g ≠ 1 → g ^ fi22CentSylowField s 1 = 1 →
      ∃ w < fi22CentSylowField s 7, ∃ t ∈ fi22CentSylowSub s, ∃ j, 0 < j ∧
        j < fi22CentSylowField s 1 ∧ g = t * fi22SylX s w ^ j * t⁻¹) ∧
    (∀ w < fi22CentSylowField s 7,
      fi22SylX s w ≠ 1 ∧ fi22SylX s w ^ fi22CentSylowField s 1 = 1 ∧
      fi22SylX s w ∈ fi22H (fi22CentSylowField s 0) ∧
      fi22SylH s w ∈ fi22H (fi22CentSylowField s 0) ∧
      ∃ k, (fi22SylX s w * fi22SylH s w * fi22SylX s w * (fi22SylH s w)⁻¹) ^ k ≠ 1 ∧
        ((fi22SylX s w * fi22SylH s w * fi22SylX s w * (fi22SylH s w)⁻¹) ^ k) ^ 2 = 1) :=
  Certificates.certificate2072 s hs

end CFSG.Sporadic.FischerOddCore

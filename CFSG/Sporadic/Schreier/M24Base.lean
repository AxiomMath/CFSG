
module

public import CFSG.Sporadic.Schreier.M24CheckBase
public import CFSG.Monster.B.Mathieu.M24Order
public import CFSG.Sporadic.Schreier.Outer
public import CFSG.Sporadic.Schreier.M24Data
public meta import CFSG.Sporadic.Schreier.M24Data
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Monster.B.Mathieu.M24CheckInputs

@[expose] public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Monster.B.Mathieu
open CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem m24_card : Nat.card NativeSporadic.M24 = 244823040 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h⟩ := fam_M24_order
  exact h

theorem m24Certificate_originalSubgroup :
    m24Certificate.originalSubgroup = NativeSporadic.M24 := by
  rw [m24Certificate, certificate_originalSubgroup, m24_eq]
  congr 1
  ext g
  simp

end CFSG.Sporadic.Schreier

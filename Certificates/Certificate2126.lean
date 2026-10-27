
module

public import CFSG.Sporadic.ONOddCore.PrimPt
public import CFSG.Sporadic.Schreier.ONSchreierData
import Certificates.Kernel.Sporadic.ONPrim.Group

public section

namespace Certificates

open CFSG.ONSchreier CFSG.Sporadic.ONOddCore in
theorem certificate2126 : 
    (∀ h ∈ lineSubgroup, h 0 = 0) ∧
      (∀ i (hi : i < 5), Nat.card (MulAction.orbit lineSubgroup (primPt hi)) =
        primSizes.getD i 0 ∧ ∀ y ∈ MulAction.orbit lineSubgroup (primPt hi), (primPt hi : ℕ) ≤ y) ∧
      (∀ y : Fin nL, ∃ i, ∃ hi : i < 5, y ∈ MulAction.orbit lineSubgroup (primPt hi)) ∧
      MulAction.IsPreprimitive Pl (Fin nL) :=
  CertificateChecks.KernelSpor.ONPrim.prim_cert

end Certificates

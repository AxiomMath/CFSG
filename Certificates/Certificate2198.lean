
module

public import Certificates.Certificate2198Base
public import Certificates.Data.CFSGNative.SporadicSchreier.Count

public import CFSG.Sporadic.Schreier.M24Data
public meta import CFSG.Sporadic.Schreier.M24Data
import Certificates.Kernel.SporSch.Mathieu.M24Facts
import Lean.Data.Json
import Mathlib.Data.ZMod.Basic

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu in
open CFSG.Sporadic.Schreier.Native in
theorem certificate2198 : (m24Certificate.check = true)
    ∧ (ordTest 24 2 (toTable m24gA) = true ∧ ordTest 24 3 (toTable m24gB) = true ∧
      pairTest 24 23 12 2 3 (toTable m24gA) (toTable m24gB) = true
    )
    ∧ ((orderTables m24Certificate 2).length = 43263 ∧
      (orderTables m24Certificate 3).length = 712448 ∧
      CFSG.Sporadic.Schreier.Native.classOK 24 (pairTables m24gA m24gB) (pairTables m24gA⁻¹ m24gB⁻¹)
        (orderTables m24Certificate 2) 40000 = true ∧
      CFSG.Sporadic.Schreier.Native.classTotal 24 (pairTables m24gA m24gB)
        (pairTables m24gA⁻¹ m24gB⁻¹) (orderTables m24Certificate 2)
        (orderTables m24Certificate 3) 40000 23 12 2 3 =
        979292160
    ) := KernelSporSch.M24OC.facts2198

end Certificates

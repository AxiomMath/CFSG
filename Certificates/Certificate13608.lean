module

public import CFSG.Sporadic.HNSchreier.LocalOuter
public import CFSG.Sporadic.HNSchreier.VectorData
public import Certificates.Kernel.SporSch.HN.C13608
public import Certificates.Certificate2102

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native Matrix in
theorem certificate13608 : {x : X | PK x.val ⬝ᵥ ((formM * (matJ (aJ * ((aJ * bJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ *
      aJ * bJ * aJ)⁻¹ * bJ * (aJ * bJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ))) +
      matJ (aJ * ((aJ * bJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ)⁻¹ * bJ *
      (aJ * bJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ))) ^ 2)) *ᵥ PK x.val) = 1}.ncard =
      166459 ∧
    {x : X | hWordJ [2, 4, 5, 8, 5, 4, 2] • x = x}.ncard = 50 :=
  KernelSporSch.HN13608.facts

end Certificates

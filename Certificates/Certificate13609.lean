module

public import CFSG.Sporadic.HNSchreier.FALocal
public import Certificates.Kernel.SporSch.HN.C13609
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107
public import Certificates.Certificate2109
public import Certificates.Certificate16041

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier in
theorem certificate13609 : Nat.card (Subgroup.centralizer ({sJ 2} : Set JH) ⊓
      Subgroup.centralizer ({c3J 6 * c3J 0 * c3J 0} : Set JH) : Subgroup JH) ≤ 30 ∧
    orderOf (c3J 6 * c3J 0 * c3J 0) = 5 :=
  KernelSporSch.HN13609.facts

end Certificates

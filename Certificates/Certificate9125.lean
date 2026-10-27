module

import Certificates.Kernel.McL.Bridge
public import CFSG.Sporadic.McL.Simple
public import Certificates.Certificate9126
public import Certificates.Data.CFSGNative.Bridge.SurjA

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Presentation CFSG.Sporadic.Presentation.McL in
open CFSG.CosetTable CFSG.Certificates CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native in
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open scoped commutatorElement in
open CFSG.Sporadic.McL (a b J orb rep_alpha rep_alpha_inv rep_beta actionChecks_parts) in
theorem certificate9125 : Finite TauCeti.SporadicName.McL.Group ∧
    Nat.card TauCeti.SporadicName.McL.Group ≤ 898128000 := KernelMcL.mcl

end Certificates

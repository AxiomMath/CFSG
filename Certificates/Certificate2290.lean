module

public import CFSG.Sporadic.SuzOddCore.CTIDefs
import Certificates.Kernel.Sporadic.OddCore.SuzCTFacts

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSpor.SuzCT in
open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four in
theorem certificate2290 : (CFSG.Sporadic.SuzOddCore.fixList 0).length = 42 ∧ (CFSG.Sporadic.SuzOddCore.fixList 1).length = 54 ∧
    ∀
      (h0 : (CFSG.Sporadic.SuzOddCore.fixList 0).length = 42) (h1 : (CFSG.Sporadic.SuzOddCore.fixList 1).length = 54),
    (Enumerates (rho0Of h0).range (enumOf 42 (kGens 0) 40320).tabs.toList ∧
      Nat.card (rho0Of h0).range = 40320 ∧
      Nat.card (suzDOf h0) = 20160 ∧
      (∀ k < 22, ∀ x ∈ suzDOf h0, kpermOf h0 k * x * (kpermOf h0 k)⁻¹ ∈ suzDOf h0 ∧
        (kpermOf h0 k)⁻¹ * x * kpermOf h0 k ∈ suzDOf h0) ∧
      Function.Injective (classFunOf h0) ∧ Function.Surjective (classFunOf h0) ∧
      (∀ l, Nat.card (classFunOf h0 l).carrier = classSizes.getD l 0) ∧
      Enumerates (suzDOf h0) (enumOf 42 dGens 20160).tabs.toList) ∧
    (Nat.card (rho1Of h1).range = 1658880 ∧
      Nat.card (suzQbarOf h1) = 64 ∧
      (∀ k < 10, ∀ x ∈ suzQbarOf h1, kperm1Of h1 k * x * (kperm1Of h1 k)⁻¹ ∈ suzQbarOf h1) ∧
      (∀ i < 6, ∀ j < 6, qpermOf h1 i * qpermOf h1 j = qpermOf h1 j * qpermOf h1 i) ∧
      ∀ y ∈ (rho1Of h1).range, (∀ j < 6, y * qpermOf h1 j = qpermOf h1 j * y) → y ∈ suzQbarOf h1) :=
  ⟨facts0.1.1, facts1.1.1, fun h0 h1 =>
    have e := entry0 h0
    ⟨⟨e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1, e.2.2.2.2.2.1, e.2.2.2.2.2.2,
      suzD_enumerates h0⟩, entry1 h1⟩⟩

end Certificates

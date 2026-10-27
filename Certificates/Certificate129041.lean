module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22CoverDefs
import Certificates.Kernel.SlpRelC.Fi22Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic in
theorem certificate129041 : ∃ p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n : CFSG.Blueprint.NativeSporadic.Fi22,
    Fi22CoverData p₀ p₁ p₂ q₀ q₁ q₂ z dA dB n := KernelSlpRel.fi22_coverData_exists

end Certificates

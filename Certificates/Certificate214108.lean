module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KilledPlaneTransport
import Certificates.Kernel.E7Plane.Assembly

public section

namespace Certificates

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore in
theorem certificate214108 : ∀ (φ ψ : Multiplicative (Fin Tag.E7.rank → ℤ) →* Z3) (w : WeylGroup .E7),
    w ∈ charStabilizer φ → w ∈ charStabilizer ψ →
      w ∈ kernelWeylGroup (φ.prod ψ) ∨ CyclicTriple .E7 (kernelRoots (φ.prod ψ)) w :=
  CFSG.KD.E7Plane.e7Plane_pair_kernel

end Certificates

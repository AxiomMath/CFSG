module

public import CFSG.Sporadic.Schreier.Co1LocalOrbitInputs
public meta import CFSG.Sporadic.Schreier.Co1OrbData
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData
public meta import CFSG.Sporadic.Schreier.Co1SplitCheck
import Certificates.Kernel.SporSch.Co1.Orb

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.ElemThree Matrix in
theorem certificate2140 : (∀ k, treeOK k = true ∧ treeClosed k = true ∧
      ∀ c ∈ treeCodes k, encodeF (decodeF c) = c) ∧
    (∀ f, ∃ k, encodeF f ∈ treeCodes k) ∧ (∀ f, decodeF (encodeF f) = f) ∧
    (∀ f, encodeF f ∈ treeCodes 1 ↔ ∃ j, f = γ j ∨ f = -γ j) := KernelSporSch.Co1Orb.facts

end Certificates

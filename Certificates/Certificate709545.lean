
module

public import Certificates.Certificate709545Base

public import Mathlib.Data.Fin.VecNotation
import Certificates.Kernel.E7Orbit.Glue

public section

public section

namespace Certificates

open Certificates.OmegaSevenMax in
theorem certificate709545 : ∃ (p : Fin 3159 → Finset V) (c : Fin 3159 → Fin 4) (r : Fin 4 → Fin 3159),
    Function.Injective p ∧ p 0 = rootSetV ∧
    (∀ i, ∃ L : List (V × V), (∀ x ∈ L, qV x.1 = 1 ∧ qV x.2 = 1) ∧
      p i = rootSetV.image (pairWord L)) ∧
    (∀ i, ∃ w : List (Fin 6), p i = (p (r (c i))).image (hWord w)) ∧
    (∀ i, c i = 0 ↔ i = 0) ∧
    (∀ d, (Finset.univ.filter (c · = d)).card = ![1, 288, 630, 2240] d) ∧
    ∀ j, rootSetV.image (hV j) = rootSetV :=
  CertificateChecks.KernelE7Orbit.orbit_facts

end Certificates

end

end

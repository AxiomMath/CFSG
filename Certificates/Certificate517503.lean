module

public import Certificates.Kernel.AE6Sm.Facts

public section

namespace Certificates

open CertificateChecks

open Certificates.AE6Model CFSG.EvenSmallLie.OmegaEight in
theorem certificate517503 : (CFSG.Certificates.ValidSchreier (sQ ()) ∧ CFSG.Certificates.ValidSchreier (czQ ())) ∧
    Nat.card (Subgroup.closure {g | g ∈ sGens ()}) = 4096 ∧
    Nat.card (Subgroup.closure {g | g ∈ czGens ()}) = 110592 ∧
    ((∀ g ∈ czGens (), g * z0 () = z0 () * g ∧ g * g = 1) ∧
      (∀ g ∈ sGens (), g * z0 () = z0 () * g) ∧ cutPerm () * z0 () = z0 () * cutPerm () ∧
      ∀ c ∈ conjPerms (), c * z0 () = z0 () * c) ∧
    1575 ≤ (CFSG.Sporadic.Schreier.conjClass omegaT (z0 ())).ncard ∧
    (CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.Q8Rel ((k0Gens ()).getD 0 1)
        ((k0Gens ()).getD 1 1) ∧
      (k0Gens ()).getD 0 1 * (k0Gens ()).getD 0 1 = z0 () ∧ (twinPairs ()).length = 4) ∧
    (∀ g ∈ czGens (), ∀ p ∈ twinPairs (), ∃ q ∈ twinPairs (),
      g * p.1 * g⁻¹ ∈ Subgroup.closure {q.1, q.2} ∧
        g * p.2 * g⁻¹ ∈ Subgroup.closure {q.1, q.2}) ∧
    ∀ x ∈ Subgroup.closure {g | g ∈ sGens ()}, ∀ y ∈ Subgroup.closure {g | g ∈ sGens ()},
      x * x = z0 () → y * y = z0 () →
      (cutPerm ())⁻¹ * x * cutPerm () ∈ Subgroup.closure {g | g ∈ sGens ()} →
      (cutPerm ())⁻¹ * y * cutPerm () ∈ Subgroup.closure {g | g ∈ sGens ()} → x * y * x = y →
      (∃ p ∈ twinPairs (), x ∈ Subgroup.closure {p.1, p.2} ∧ y ∈ Subgroup.closure {p.1, p.2}) ∨
        5 ≤ Set.ncard {J | ∃ c ∈ conjPerms (),
          J = (Subgroup.closure {x, y}).map (MulAut.conj c).toMonoidHom} :=
  KernelAE6Sm.facts517503

end Certificates

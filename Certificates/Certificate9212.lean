module

import Certificates.Kernel.J4Hub.Card
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.J4.Group
public import Certificates.Certificate9357

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge TauCeti in
theorem certificate9212 : ∃ g : ℕ → CFSG.Sporadic.J4.J,
    (∀ v ∈ Sporadic.j4Presentation.relatorLetters, wordProd g v = 1) ∧
      Subgroup.closure {g 0, g 1, g 2} = ⊤ := by
  refine ⟨KernelJ4Hub.gen, fun v hv => ?_, ?_⟩
  · rw [KernelBounds.J4.rels_eq] at hv
    exact KernelJ4Hub.rels_XYT v hv
  · have e : KernelJ4Hub.gen 0 = KernelJ4Hub.X ∧ KernelJ4Hub.gen 1 = KernelJ4Hub.Y ∧
        KernelJ4Hub.gen 2 = KernelJ4Hub.T := by
      simp [KernelJ4Hub.gen]
    rw [e.1, e.2.1, e.2.2]
    exact KernelJ4Hub.xyt_top

end Certificates

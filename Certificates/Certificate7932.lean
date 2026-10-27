module

public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictJFacts
import Certificates.Kernel.J4NPVerdict.Glue
import Certificates.Kernel.J4NPVerdict.C7932

public section

namespace Certificates

open CFSG.KC.J4NPV CertificateChecks.KernelJ4NPV CFSG.Quasithin.KGC31.J4M4

theorem certificate7932 : CFSG.ASVolI.burnsideJ4NP_FFact 89 := by
  have hall := vj_chunk (f := fB vjT) (n := 1) (m := 1) (ds := CFSG.ASVolI.burnsideJ4NP_vjF)
    (by decide) (fun i hi => by
      interval_cases i
      exact vj7932c0)
  obtain ⟨x, hx⟩ := fB_le vj_tabs (hall _ (List.mem_singleton_self CFSG.ASVolI.burnsideJ4NP_vjNode89))
  have e : Set.range fJ = {y | ∃ j < 10, y = fJn j} := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.1, j.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  refine ⟨x, ?_⟩
  rw [CFSG.ASVolI.burnsideJ4NP_F, e]
  exact hx

end Certificates

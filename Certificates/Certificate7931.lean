module

public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictJFacts
import Certificates.Kernel.J4NPVerdict.Glue
import Certificates.Kernel.J4NPVerdict.C7931

public section

namespace Certificates

open CFSG.KC.J4NPV CertificateChecks.KernelJ4NPV

theorem certificate7931 : ∀ k ∈ CFSG.ASVolI.burnsideJ4NP_vjHIds, CFSG.ASVolI.burnsideJ4NP_NPFact k := by
  refine fun k hk => ?_
  have hall := vj_chunk (f := npB vjT) (n := 6) (m := 2) (ds := CFSG.ASVolI.burnsideJ4NP_vjH)
    (by decide) (fun i hi => by
      interval_cases i
      exacts [vj7931c0, vj7931c1])
  have e : CFSG.ASVolI.burnsideJ4NP_vjH.map CFSG.J4Tree.VerdictJ.NPData.node =
      CFSG.ASVolI.burnsideJ4NP_vjHIds := rfl
  rw [← e] at hk
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hk
  exact npB_normalizer vj_tabs vj_comm (hall d hd)

end Certificates

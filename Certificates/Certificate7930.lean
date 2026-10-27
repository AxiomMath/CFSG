module

public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictJFacts
import Certificates.Kernel.J4NPVerdict.Glue
import Certificates.Kernel.J4NPVerdict.C7930A
import Certificates.Kernel.J4NPVerdict.C7930B

public section

namespace Certificates

open CFSG.KC.J4NPV CertificateChecks.KernelJ4NPV

theorem certificate7930 : ∀ k ∈ CFSG.ASVolI.burnsideJ4NP_vjT3Ids, CFSG.ASVolI.burnsideJ4NP_NPFact k := by
  refine fun k hk => ?_
  have hall := vj_chunk (f := npB vjT) (n := 8) (m := 6) (ds := CFSG.ASVolI.burnsideJ4NP_vjT3)
    (by decide) (fun i hi => by
      interval_cases i
      exacts [vj7930c0, vj7930c1, vj7930c2, vj7930c3, vj7930c4, vj7930c5])
  have e : CFSG.ASVolI.burnsideJ4NP_vjT3.map CFSG.J4Tree.VerdictJ.NPData.node =
      CFSG.ASVolI.burnsideJ4NP_vjT3Ids := rfl
  rw [← e] at hk
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hk
  exact npB_normalizer vj_tabs vj_comm (hall d hd)

end Certificates

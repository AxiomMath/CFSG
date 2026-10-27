module

public import CFSG.ClassicalInvolution.Q3.Q3ZPres
import Certificates.Kernel.CosPres.F270002
import CFSG.Certificates.Kernel.Q3Coll.Index

public section

namespace Certificates

theorem certificate270002 : CFSG.ClassicalInvolution.Q3.Q3Z.V6Collapse := by
  refine CFSG.KC.Q3Coll.v6Collapse_of_tables fun k hk => ?_
  fin_cases k
  all_goals first | exact absurd hk (by decide) | skip
  exacts [CFSG.KBFact.F270002k4, CFSG.KBFact.F270002k5, CFSG.KBFact.F270002k6,
    CFSG.KBFact.F270002k7, CFSG.KBFact.F270002k8, CFSG.KBFact.F270002k9, CFSG.KBFact.F270002k10,
    CFSG.KBFact.F270002k11, CFSG.KBFact.F270002k12, CFSG.KBFact.F270002k13,
    CFSG.KBFact.F270002k14, CFSG.KBFact.F270002k15, CFSG.KBFact.F270002k16,
    CFSG.KBFact.F270002k17, CFSG.KBFact.F270002k18, CFSG.KBFact.F270002k19,
    CFSG.KBFact.F270002k20, CFSG.KBFact.F270002k21, CFSG.KBFact.F270002k22,
    CFSG.KBFact.F270002k23]

end Certificates

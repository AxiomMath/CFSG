module

public import CFSG.ClassicalInvolution.Q3.Q3TWCollTD
import Certificates.Kernel.CosPres.F270004A
import CFSG.Certificates.Kernel.Q3Coll.Index

public section

namespace Certificates

theorem certificate270004 : CFSG.ClassicalInvolution.Q3.Q3TW.TD4Collapse := by
  refine CFSG.KC.Q3Coll.td4Collapse_of_tables fun k hk => ?_
  fin_cases k
  all_goals first | exact absurd hk (by decide) | skip
  exacts [CFSG.KBFact.F270004k4, CFSG.KBFact.F270004k5, CFSG.KBFact.F270004k6,
    CFSG.KBFact.F270004k7, CFSG.KBFact.F270004k8, CFSG.KBFact.F270004k9, CFSG.KBFact.F270004k10,
    CFSG.KBFact.F270004k11, CFSG.KBFact.F270004k12, CFSG.KBFact.F270004k13,
    CFSG.KBFact.F270004k14, CFSG.KBFact.F270004k15, CFSG.KBFact.F270004k16,
    CFSG.KBFact.F270004k17, CFSG.KBFact.F270004k18, CFSG.KBFact.F270004k19,
    CFSG.KBFact.F270004k20, CFSG.KBFact.F270004k21, CFSG.KBFact.F270004k22,
    CFSG.KBFact.F270004k23]

end Certificates

module

public import CFSG.ClassicalInvolution.Q3.Q3TWCollB
import Certificates.Kernel.CosPres.F270003
import CFSG.Certificates.Kernel.Q3Coll.Index

public section

namespace Certificates

theorem certificate270003 : CFSG.ClassicalInvolution.Q3.Q3TW.B3Collapse := by
  refine CFSG.KC.Q3Coll.b3Collapse_of_tables fun k hk => ?_
  fin_cases k
  all_goals first | exact absurd hk (by decide) | skip
  exacts [CFSG.KBFact.F270003k4, CFSG.KBFact.F270003k5, CFSG.KBFact.F270003k6,
    CFSG.KBFact.F270003k7, CFSG.KBFact.F270003k8, CFSG.KBFact.F270003k9, CFSG.KBFact.F270003k10,
    CFSG.KBFact.F270003k11, CFSG.KBFact.F270003k12, CFSG.KBFact.F270003k13,
    CFSG.KBFact.F270003k14, CFSG.KBFact.F270003k15, CFSG.KBFact.F270003k16,
    CFSG.KBFact.F270003k17, CFSG.KBFact.F270003k18, CFSG.KBFact.F270003k19,
    CFSG.KBFact.F270003k20, CFSG.KBFact.F270003k21, CFSG.KBFact.F270003k22,
    CFSG.KBFact.F270003k23]

end Certificates

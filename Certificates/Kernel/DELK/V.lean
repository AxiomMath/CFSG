module

public import Certificates.Kernel.DELK.D
public import Certificates.Data.Kernel.DELKWF

public section

namespace CFSG.KD.DELK

open Certificates.DELK

theorem pairsOK : kPairsOK P = true := by decide +kernel

theorem conjShapes : kConjShapes C = true := by decide +kernel

theorem neg_pairsOK : (!kPairsOK (P.map fun l => l.map fun q => (q.1.tail, q.2))) = true := by
  decide +kernel

theorem neg_conjShapes : (!kConjShapes (C.map fun c => (c.1, c.2.1, c.2.2.1.tail, c.2.2.2))) =
    true := by
  decide +kernel

end CFSG.KD.DELK

end

module

public import CFSG.Sporadic.ONOddCore.LiftPayload
public meta import CFSG.Sporadic.ONOddCore.LiftPayload
public import CFSG.Sporadic.ONOddCore.LiftCountInputs
public import Certificates.Certificate2121

public section

namespace CFSG.Sporadic.ONOddCore

theorem cand_count_cert :
    (List.range 12).map (fun k => (liftIdxs (liftData.cands.getD k [])).length) =
        [4, 0, 0, 4, 0, 0, 0, 0, 0, 4, 4, 0] ∧
      (List.range 12).all (fun k => (liftIdxs (liftData.cands.getD k [])).Nodup) = true :=
  Certificates.certificate2121

end CFSG.Sporadic.ONOddCore

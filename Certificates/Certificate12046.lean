module

public import CFSG.LieType.Multipliers.F42Data
import Certificates.Kernel.Misc.F42Bridge

public section

namespace Certificates

open CFSG.LieType.Multipliers.F42 in
theorem certificate12046 : (List.range 48).all (liftOK lifts) = true ∧ pairsOK lifts = true ∧
    (List.range 48).all (wordOK lifts) = true ∧ negOK lifts 0 35 = true := CFSG.KD.Misc.F42.facts

end Certificates

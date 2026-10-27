
module

public import CFSG.Sporadic.Schreier.RuCheckOrbLBBase

public import CFSG.Sporadic.Schreier.RuOrbLDefs
public meta import CFSG.Sporadic.Schreier.RuOrbLDefs
public import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs
public import Certificates.Certificate2255

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem ruOrbLB_check :
    (List.range 19).map ruCentCount = ruCentCounts ∧
    (List.range 19).map (fun k => ruOrd14 (compA 4060 ruA0A (ruRepZA k))) =
      [false, false, false, true, false, false, true, false, false, false, false, true, false,
        false, false, false, false, false, false] ∧
    count3 4060 ruLevC ruSqZA = 816 ∧
    [ruFibCount 3, ruFibCount 6, ruFibCount 11] = [0, 0, 4] :=
  Certificates.certificate2255

end CFSG.Sporadic.RuSchreier

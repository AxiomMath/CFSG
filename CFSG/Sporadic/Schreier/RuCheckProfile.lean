module

public import CFSG.Sporadic.Schreier.RuCheckSylow
public meta import CFSG.Sporadic.Schreier.RuCheckSylow
public import CFSG.Sporadic.Schreier.RuCheckProfileInputs
public import Certificates.Certificate2257

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem ruProfile_check :
    ((List.range 8).map fun v =>
      all2 1920 (rawLevels 1920 (ruField1920 4) (ruBaseArr 1920 ruRBase))
      (fun g => ruOrd8F (compA 1920 (ruTv v) g))) =
      [false, false, false, false, true, false, false, false] :=
  Certificates.certificate2257

end CFSG.Sporadic.RuSchreier

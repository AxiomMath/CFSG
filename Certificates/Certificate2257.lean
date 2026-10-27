module

public import CFSG.Sporadic.Schreier.RuCheckProfileInputs
public meta import CFSG.Sporadic.Schreier.RuCheckSylow
import Certificates.Kernel.SporSch.Ru.R2257P

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate2257 : ((List.range 8).map fun v =>
    all2 1920 (rawLevels 1920 (ruField1920 4) (ruBaseArr 1920 ruRBase))
    (fun g => ruOrd8F (compA 1920 (ruTv v) g))) =
    [false, false, false, false, true, false, false, false] := KernelSporSch.RuP.facts

end Certificates

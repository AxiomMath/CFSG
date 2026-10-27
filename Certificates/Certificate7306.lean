module

public import CFSG.Quasithin.Recognition.RuRank3J55DataInputs
import Certificates.Kernel.SporSch.Ru.Glue7048

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem certificate7306 :
    (allLt 4060 fun x => (ruInD x && ruRowA ruTI1 x) ==
        (ruFLab[x]! == 2 || ruFLab[x]! == 6 || ruFLab[x]! == 7)) = true ∧
    labCount 4060 ruFLab 7 = 10 ∧ labCount 4060 ruFLab 6 = 80 ∧ labCount 4060 ruFLab 2 = 640 ∧
    ruFLab[2325]! = 7 ∧ ruFLab[149]! = 6 ∧ ruFLab[2]! = 2 ∧
    isInvA 4060 (ruTreeArr 2325) (ruTI 2325) = true ∧
    isInvA 4060 (ruTreeArr 149) (ruTI 149) = true ∧
    isInvA 4060 (ruTreeArr 2) (ruTI 2) = true ∧
    ruCommonCnt ruTI1 (ruTI 2325) = 217 ∧ ruCommonCnt ruTI1 (ruTI 149) = 345 ∧
    ruCommonCnt ruTI1 (ruTI 2) = 281 := KernelSporSch.Glue7048.c7306

end Certificates

module

public import CFSG.Quasithin.Recognition.RuRank3J55DataInputs
import Certificates.Kernel.SporSch.Ru.Q7305

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem certificate7305 :
    ((allLt 4060 fun x => (ruInD x && ruRowA ruTIG0 x) == (ruELab[x]! == 2)) = true ∧
       (allLt 4060 fun x => (ruInD x && !ruRowA ruTIG0 x) == (ruELab[x]! == 1)) = true ∧
       (allLt 4060 fun x => (ruInS x && ruRowA ruTIG0 x) == (ruELab[x]! == 3)) = true ∧
       ruELab[2]! = 2 ∧
       (∀ b : Fin 9 → Bool, selCount 4060 ruELab b = 975 →
         (allLt 4060 fun x => !(bAt b ruELab[x]!) || ruInS x) = true →
         (allLt 4060 fun x => bAt b ruELab[x]! == (ruELab[x]! == 3)) = true))
    ∧ ((allLt 2 fun i => isInvA 4060 (ruFrobArr i) (invCand 4060 (ruFrobArr i)) &&
         ruSift 4060 (ruField4060 3) ruJoinBase (ruFrobArr i) && (ruFrobArr i)[0]! == 0 &&
         (ruFrobArr i)[ruG0]! == ruG0 && (ruFrobArr i)[2]! == 2) = true ∧
       eqA 4060 (CFSG.Sporadic.RuSchreier.powA 4060 (ruFrobArr 0) 5) (idA 4060) = true ∧
       eqA 4060 (ruFrobArr 0) (idA 4060) = false ∧
       eqA 4060 (CFSG.Sporadic.RuSchreier.powA 4060 (ruFrobArr 1) 4) (idA 4060) = true ∧
       eqA 4060 (CFSG.Sporadic.RuSchreier.powA 4060 (ruFrobArr 1) 2) (idA 4060) = false ∧
       eqA 4060 (ruConjArr (ruFrobArr 1) (ruFrobArr 0))
         (CFSG.Sporadic.RuSchreier.powA 4060 (ruFrobArr 0) 2) = true) := KernelSporSch.Q7305.c7305

end Certificates

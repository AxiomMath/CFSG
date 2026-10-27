
module

public import CFSG.Quasithin.Recognition.RuRank3RuGraphDataInputs
import Certificates.Kernel.SporSch.Ru.Glue7046

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem certificate7046 :
    (orbCheck 4060 ruR0Arrs = true ∧
       (allLt 4060 fun x => x == 0 || ruQLab[x]! != ruQLab[0]!) = true ∧
       (allLt 1755 fun j => ruQLab[ruDArr[j]!]! == ruQLab[1]!) = true ∧
       labCount 4060 ruQLab ruQLab[1]! = 1755 ∧ labCount 4060 ruQLab ruQLab[ruG0]! = 2304 ∧
       (allLt 4060 fun x => ruQLab[x]! == ruQLab[0]! || ruQLab[x]! == ruQLab[1]! ||
         ruQLab[x]! == ruQLab[ruG0]!) = true ∧
       ruQLab[1]! ≠ ruQLab[ruG0]! ∧ ruQLab[0]! ≠ ruQLab[ruG0]! ∧
       isInvA 4060 (ruTreeArr 1) ruTI1 = true ∧ isInvA 4060 (ruTreeArr ruG0) ruTIG0 = true)
    ∧ ((allLt 2 fun i => isInvA 4060 (ruFGArr i) (invCand 4060 (ruFGArr i)) &&
         ruSift 4060 (ruField4060 3) ruJoinBase (ruFGArr i) && (ruFGArr i)[0]! == 0 &&
         (ruFGArr i)[1]! == 1) = true ∧
       (allLt 2 fun i => isInvA 4060 (ruEGArr i) (invCand 4060 (ruEGArr i)) &&
         ruSift 4060 (ruField4060 3) ruJoinBase (ruEGArr i) && (ruEGArr i)[0]! == 0 &&
         (ruEGArr i)[ruG0]! == ruG0) = true ∧
       orbCheck 4060 ruFGArrs = true ∧ (allLt 4060 fun x => decide (ruFLab[x]! < 8)) = true ∧
       orbCheck 4060 ruEGArrs = true ∧ (allLt 4060 fun x => decide (ruELab[x]! < 9)) = true)
    ∧ (ruA0A[0]! = 1 ∧ ruA0A[1]! = 0)
    ∧ ((∀ b : Fin 8 → Bool, selCount 4060 ruFLab b = 1755 → bAt b ruFLab[0]! = true →
         bAt b ruFLab[1]! = false →
         (allLt 4060 fun x => bAt b ruFLab[x]! == ruRowA ruTI1 x) = true ∨
         (allLt 4060 fun x => !(bAt b ruFLab[x]!) || !(ruInS x)) = true) ∧
       (∀ b : Fin 9 → Bool, selCount 4060 ruELab b = 1755 → bAt b ruELab[0]! = false →
         bAt b ruELab[ruG0]! = false →
         (allLt 4060 fun x => bAt b ruELab[x]! == ruRowA ruTIG0 x) = true ∨
         (allLt 4060 fun x => bAt b ruELab[x]! == (ruQLab[x]! == ruQLab[1]!)) = true)) := KernelSporSch.Glue7046.c7046

end Certificates

module

public import CFSG.RankThree.PartTwo.KFacts.L34NormalizerMaxInputs

public section

namespace Certificates.Data.L34QEight

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.L34
open CFSG.RankThree.PartTwo.KFacts.L34Max

@[expose] def q1 : Equiv.Perm (Fin 21) := tab (n0a * n0b)

@[expose] def q2 : Equiv.Perm (Fin 21) := tab (n0b * n0a * n0a)

@[expose] def qList : List (Equiv.Perm (Fin 21)) :=
  [1, q1, q1 ^ 2, q1 ^ 3, q2, q1 * q2, q1 ^ 2 * q2, q1 ^ 3 * q2].map tab

@[expose] def qClosed : Bool :=
  decide qList.Nodup && (qList.all fun a => qList.all fun b => qList.contains (a * b)) &&
    qList.all fun a => qList.contains a⁻¹

@[expose] def conjs (qs : List (Equiv.Perm (Fin 21))) (x : Equiv.Perm (Fin 21)) :
    List (Equiv.Perm (Fin 21)) :=
  1 :: qs.flatMap fun q => [tab (q * x * q⁻¹), tab (q * x⁻¹ * q⁻¹)]

@[expose] def wordOK (qs : List (Equiv.Perm (Fin 21))) (x : Equiv.Perm (Fin 21)) : Bool :=
  let cs := conjs qs x
  cs.any fun a => cs.any fun b => cs.any fun c => orderIs (x * a * b * c) 3

@[expose] def closureCheck : Bool :=
  let qs := qList
  (elemsT QP21).all fun x => !(orderIs x 5 || orderIs x 7) || wordOK qs x

end Certificates.Data.L34QEight

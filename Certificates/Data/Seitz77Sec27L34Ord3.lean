module

public import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.GH74.KGroups.L34
public meta import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.GH74.KGroups.L34

public section

namespace Certificates.Seitz77Sec27

open CFSG.KGroups.Native CFSG.GH74.KGroups.NativeChecks CFSG.GH74.KGroups.L34

@[expose] def l34Ord3CheckL (L : List (Array Nat)) : Bool :=
  decide ((L.filter fun a => orderIsA 42 a 3).length = 2240) &&
    match L.filter (fun a => orderIsA 42 a 3) with
    | a :: _ => decide (centLenA 42 L a = 9)
    | [] => false

@[expose] def l34Ord3Check : Bool := l34Ord3CheckL (enumA QP)

end Certificates.Seitz77Sec27

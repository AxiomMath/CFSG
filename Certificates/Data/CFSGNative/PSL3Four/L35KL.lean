module

public import Certificates.Data.CFSGNative.PSL3Four.L34KL

public section

namespace CFSG.PSL3Four.Native

@[expose] def invertsE9 (t : Tab) : Bool :=
  comp 42 t a₀T == comp 42 (powTab 42 a₀T 2) t && comp 42 t b₀T == comp 42 (powTab 42 b₀T 2) t

@[expose] def hasInvol (N : Array Tab) (x : Tab) : Bool :=
  anyBelow N.size fun k =>
    comp 42 N[k]! N[k]! == idTab 42 && !(N[k]! == idTab 42) &&
      comp 42 x N[k]! == comp 42 N[k]! x

@[expose] def l35Elem (E9 : Array Tab) (ES N : Array Tab) (x : Tab) (c : Nat) : Bool :=
  (!(normsE9 E9 x && decide (60 ≤ c)) || hasInvol N x) &&
    (!(!memTab ES x && decide (60 ≤ c)) || c == 60)

@[expose] def l35KLCheck (ES ER : Array Tab) : Bool :=
  let E9 := e9T ()
  let N := ES.filter invertsE9
  memTab ES a₀T && memTab ES b₀T &&
    powTab 42 a₀T 3 == idTab 42 && powTab 42 b₀T 3 == idTab 42 &&
    comp 42 a₀T b₀T == comp 42 b₀T a₀T &&
    (allBelow 9 fun i => allBelow 9 fun j => i == j || !(E9[i]! == E9[j]!)) &&
    (allBelow ER.size fun k =>
      !(powTab 42 ER[k]! 3 == idTab 42) ||
        l35Elem E9 ES N ER[k]! (centTabs 42 ES ER[k]!).size)

end CFSG.PSL3Four.Native

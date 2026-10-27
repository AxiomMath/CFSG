module

public import Certificates.Data.CFSGNative.PSL3Four.L34Cent

public section

namespace CFSG.PSL3Four.Native

@[expose] def normsE9 (E9 : Array Tab) (t : Tab) : Bool :=
  anyBelow 9 (fun i => comp 42 t a₀T == comp 42 E9[i]! t) &&
    anyBelow 9 (fun j => comp 42 t b₀T == comp 42 E9[j]! t)

@[expose] def commE9 (t : Tab) : Bool :=
  comp 42 t a₀T == comp 42 a₀T t && comp 42 t b₀T == comp 42 b₀T t

@[expose] def hasInvSq (N : Array Tab) (t : Tab) : Bool :=
  anyBelow N.size fun k =>
    powTab 42 N[k]! 4 == idTab 42 && !(comp 42 N[k]! N[k]! == idTab 42) &&
      comp 42 t (comp 42 N[k]! N[k]!) == comp 42 (comp 42 N[k]! N[k]!) t

@[expose] def l34KLCheck (ES ER : Array Tab) : Bool :=
  let E9 := e9T ()
  let N := ES.filter (normsE9 E9)
  memTab ES a₀T && memTab ES b₀T &&
    powTab 42 a₀T 3 == idTab 42 && powTab 42 b₀T 3 == idTab 42 &&
    comp 42 a₀T b₀T == comp 42 b₀T a₀T &&
    (allBelow 9 fun i => allBelow 9 fun j => i == j || !(E9[i]! == E9[j]!)) &&
    (allBelow ER.size fun k =>
      !(commE9 ER[k]! && powTab 42 ER[k]! 4 == idTab 42) || powTab 42 ER[k]! 2 == idTab 42) &&
    (allBelow ER.size fun k =>
      !(powTab 42 ER[k]! 3 == idTab 42 && normsE9 E9 ER[k]! &&
        decide (60 ≤ (centTabs 42 ES ER[k]!).size)) || hasInvSq N ER[k]!)

end CFSG.PSL3Four.Native

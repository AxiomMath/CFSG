module

public import Certificates.Data.CFSGNative.PSL3Four.Certificate

public section

namespace CFSG.PSL3Four.Native

@[expose] def powTab (n : Nat) (t : Tab) : Nat → Tab
  | 0 => idTab n
  | k + 1 => comp n t (powTab n t k)

@[expose] def memTab (T : Array Tab) (x : Tab) : Bool := anyBelow T.size fun k => T[k]! == x

@[expose] def zT : Tab :=
  #[11, 14, 2, 8, 17, 20, 6, 4, 13, 9, 10, 12, 0, 3, 18, 5, 16, 7, 1, 19, 15, 33, 39, 23, 34, 28, 36,
    27, 38, 24, 30, 31, 21, 32, 29, 22, 41, 37, 25, 35, 40, 26]

@[expose] def z2T (_ : Unit := ()) : Tab := comp 42 zT zT

@[expose] def centScanOK (n : Nat) (T D L : Array Tab) : Bool :=
  allBelow T.size fun k =>
    !(allBelow D.size fun a => comp n D[a]! T[k]! == comp n T[k]! D[a]!) || memTab L T[k]!

@[expose] def expOK (n : Nat) (T : Array Tab) : Bool :=
  allBelow T.size fun k => !(powTab n T[k]! 27 == idTab n) || powTab n T[k]! 3 == idTab n

@[expose] def witness (n p : Nat) (D Di : Array Tab) (y : Tab) : Bool :=
  anyBelow D.size (fun a => !(powTab n (comp n y (conjTab n D[a]! Di[a]! y)) p == idTab n)) ||
    anyBelow D.size (fun a => anyBelow D.size (fun b =>
      !(powTab n (comp n (comp n y (conjTab n D[a]! Di[a]! y)) (conjTab n D[b]! Di[b]! y)) p
        == idTab n)))

@[expose] def witOK (n p : Nat) (T D Di exc : Array Tab) (r : Tab) : Bool :=
  allBelow T.size fun k =>
    !(!(T[k]! == idTab n) && comp n (comp n (comp n r T[k]!) r) T[k]! == idTab n &&
        powTab n T[k]! p == idTab n) ||
      memTab exc T[k]! || witness n p D Di T[k]!

@[expose] def l34AutCheck (ES ER : Array Tab) : Bool :=
  let D₁ := centTabs 42 ES r₁T
  let D₂ := centTabs 42 ES r₂T
  let D₃ := centTabs 42 ES r₃T
  let D₄ := centTabs 42 ES r₄T
  let i₁ := D₁.map (invTab 42)
  let i₂ := D₂.map (invTab 42)
  let i₃ := D₃.map (invTab 42)
  let i₄ := D₄.map (invTab 42)
  memTab ER zT && !(zT == idTab 42) && powTab 42 zT 3 == idTab 42 &&
    comp 42 (comp 42 r₃T zT) r₃T == z2T &&
    notInOK ES zT && notInOK ES z2T && notInOK ES (comp 42 r₃T zT) && notInOK ES (comp 42 r₃T z2T) &&
    (allBelow D₃.size fun a => comp 42 D₃[a]! zT == comp 42 zT D₃[a]!) &&
    (allBelow ES.size fun k =>
      !(comp 42 ES[k]! zT == comp 42 zT ES[k]!) || comp 42 ES[k]! r₃T == comp 42 r₃T ES[k]!) &&
    centScanOK 42 ER D₃ #[idTab 42, zT, z2T, r₃T, comp 42 zT r₃T, comp 42 z2T r₃T] &&
    expOK 42 ER &&
    invsOK 42 D₁ i₁ && invsOK 42 D₂ i₂ && invsOK 42 D₃ i₃ && invsOK 42 D₄ i₄ &&
    witOK 42 3 ER D₁ i₁ #[] r₁T && witOK 42 5 ER D₁ i₁ #[] r₁T && witOK 42 7 ER D₁ i₁ #[] r₁T &&
    witOK 42 3 ER D₂ i₂ #[] r₂T && witOK 42 5 ER D₂ i₂ #[] r₂T && witOK 42 7 ER D₂ i₂ #[] r₂T &&
    witOK 42 3 ER D₃ i₃ #[zT, z2T] r₃T && witOK 42 5 ER D₃ i₃ #[zT, z2T] r₃T &&
    witOK 42 7 ER D₃ i₃ #[zT, z2T] r₃T &&
    witOK 42 3 ER D₄ i₄ #[] r₄T && witOK 42 5 ER D₄ i₄ #[] r₄T && witOK 42 7 ER D₄ i₄ #[] r₄T

end CFSG.PSL3Four.Native

module

public import Certificates.Data.Kernel.SporLatDcCode

public section

namespace CFSG.KC.SLDc

open CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def packDc (w : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => Nat.add a (Nat.mul (Nat.pow 2 w) (packDc w l))

@[expose] def slotDc (w K i : Nat) : Nat :=
  Nat.mod (Nat.shiftRight K (Nat.mul w i)) (Nat.pow 2 w)

@[expose] def incDc : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => Nat.blt a b && incDc (b :: l)

@[expose] def imgDc (M w K p : Nat) (y : List Nat) : Bool :=
  y.all (fun q => Nat.blt q M) && Nat.beq (slotDc w K p) (encodeSet M y)

@[expose] def omPK (actF : Nat → List Nat → List Nat) (x0 : List Nat) (nl M w n : Nat)
    (lbl rows : List (List Nat)) (par via : List Nat) (K : Nat) (R : List Nat) : Bool :=
  (lbl.headD [] == x0) && Nat.blt 0 n && Nat.beq lbl.length n && Nat.blt n (Nat.pow 2 w) &&
    lbl.all (fun x => x.all (fun q => Nat.blt q M) && Nat.blt (encodeSet M x) (Nat.pow 2 w)) &&
    (List.range nl).all (fun l => Nat.beq (rows.getD l []).length n &&
      (List.zip (rows.getD l []) lbl).all fun e => Nat.blt e.1 n && imgDc M w K e.1 (actF l e.2)) &&
    Nat.beq par.length n && Nat.beq via.length n &&
    allIdx (fun i e => Nat.beq i 0 ||
      (Nat.blt e.1 i && Nat.blt e.2 nl && Nat.beq (slotDc w (R.getD e.2 0) e.1) i)) 0
      (List.zip par via) &&
    incDc (insN (lbl.map (encodeSet M)))

@[expose] def omOKP (actF : Nat → List Nat → List Nat) (x0 : List Nat) (nl M w : Nat)
    (O : OmegaData (List Nat)) : Bool :=
  omPK actF x0 nl M w O.lbl.toList.length O.lbl.toList (O.pn.toList.map Array.toList)
    O.par.toList O.via.toList (packDc w (O.lbl.toList.map (encodeSet M)))
    ((O.pn.toList.map Array.toList).map (packDc w))

end CFSG.KC.SLDc

end

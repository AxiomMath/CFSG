module

public import Certificates.Data.Kernel.SporLatDcT

public section

namespace CFSG.KC.SLDc

open CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat

@[expose] noncomputable def omTKw (n w wi wk : Nat) (ts : Array (Array Nat)) (x0 : List Nat)
    (pts ci li : List (List Nat)) (ord : List Nat) (lbl rows : List (List Nat))
    (par via : List Nat) (P : Nat) (CI : List Nat) : Bool :=
  allRc (fun p => allRc (fun q => Nat.blt q n) p) pts && incRc (mapRc (encRc n) pts) &&
    allRc (fun c => Nat.blt c (Nat.pow 2 w)) (mapRc (encRc n) pts) &&
    Nat.ble pts.length (Nat.pow 2 wi) && Nat.beq ci.length ts.size && tabTD n w ts pts P ci &&
    (lbl.headD [] == x0) && Nat.beq li.length lbl.length &&
    zipAllRc (fun a b => allRc (fun q => Nat.blt q pts.length) a &&
      eqLRc (mapRc (slotDc w P) a) b) li lbl &&
    omPKo (fun l x => insNRc (mapRc (slotDc wi (CI.getD l 0)) x)) (li.headD []) ts.size
      pts.length wk li.length li rows par via (packDc wk (li.map (encodeSet pts.length)))
      (rows.map (packDc wk)) ord

@[expose] noncomputable def omOKTw (n w wi wk : Nat) (ts : Array (Array Nat)) (x0 : List Nat)
    (pts ci li : List (List Nat)) (ord : List Nat) (O : OmegaData (List Nat)) : Bool :=
  omTKw n w wi wk ts x0 pts ci li ord O.lbl.toList (O.pn.toList.map Array.toList) O.par.toList
    O.via.toList (packDc w (pts.map (encodeSet n))) (ci.map (packDc wi))

end CFSG.KC.SLDc

end

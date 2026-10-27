module

public import Certificates.Data.Kernel.M24G.Img
public import Certificates.Data.CFSGNative.AS91.M24TrioOne

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

@[expose] def composeL (a b : List Nat) : List Nat :=
  (List.range 24).map fun i => a.getD (b.getD i 0) 0

@[expose] def prodL (s : Nat) : List Nat :=
  (List.range 6).foldl
    (fun acc j => if s.testBit j then composeL acc (Native.tTabs.getD j #[]).toList else acc)
    Native.r121IdTab.toList

@[expose] def groupL : Bool :=
  ((List.range 6).all (fun j => prodL (1 <<< j) == (Native.tTabs.getD j #[]).toList) &&
    prodL 0 == Native.r121IdTab.toList) &&
  ((List.range 64).all fun s => (List.range 64).all fun s' =>
    composeL (prodL s) (prodL s') == prodL (s ^^^ s')) &&
  ((List.range 64).all fun s => (List.range s).all fun s' =>
    (List.range 24).any fun i => (prodL s).getD i 0 != (prodL s').getD i 0) &&
  ((List.range 64).all fun s => (prodL s).length == 24 && (prodL s).all (· < 24))

@[expose] def prodBs : List (Nat × Nat × Nat) := (List.range 63).map fun s => imgTab (prodL (s + 1))

@[expose] def fixingL (bs : List (Nat × Nat × Nat)) (t : Nat × Nat × Nat) :
    List (Nat × Nat × Nat) :=
  bs.filter fun b => (Native.octsT t).all fun o => imgF b o == o

@[expose] def witOK (b : Nat × Nat × Nat) (SL : List (List Nat)) (t : Nat × Nat × Nat) (q : Nat) :
    Bool :=
  let U := SL.getD q []
  decide (q < SL.length) && Native.trioIn t U &&
    (Native.trioIn Native.baseTrio U || !(U.all fun x => U.contains (imgF b x)))

@[expose] def fixWitOK (bs : List (Nat × Nat × Nat)) (SL : List (List Nat)) (t : Nat × Nat × Nat)
    (ws : List Nat) : Bool :=
  let fx := fixingL bs t
  fx.length == ws.length && (fx.zip ws).all fun e => witOK e.1 SL t e.2

@[expose] def fixCopW (bs : List (Nat × Nat × Nat)) (TL : List (Nat × Nat × Nat))
    (SL : List (List Nat)) (W : List (List Nat)) : Bool :=
  TL.length == W.length && (TL.zip W).all fun e => fixWitOK bs SL e.1 e.2

end CFSG.KC.M24G

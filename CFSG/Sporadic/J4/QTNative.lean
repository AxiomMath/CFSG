module

public import CFSG.Sporadic.J4.QTMask
public import Certificates.Data.CFSGNative.J4.Cert

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

@[expose] def invWord (w : List Int) : List Int := w.reverse.map fun l => -l

@[expose] def uWord (j : Nat) : List Int :=
  conjWords.getD j [] ++ zWord ++ invWord (conjWords.getD j [])

@[expose] def uTab (loc inv : Array (Array V2)) : Array (Array V2) :=
  ((List.range 11).map fun j => wordRows loc inv (uWord j)).toArray

@[expose] def etaRows (T : Array (Array V2)) (n c : Nat) : Array V2 :=
  (List.range n).foldl (fun acc j => if c.testBit j then mulRows acc (T[j]?.getD idRows) else acc)
    idRows

@[expose] def xRows (loc inv : Array (Array V2)) (ℓ : Int) : Array V2 :=
  if 0 < ℓ then loc[ℓ.toNat - 1]?.getD idRows else inv[(-ℓ).toNat - 1]?.getD idRows

@[expose] def xiRows (loc inv : Array (Array V2)) (ℓ : Int) : Array V2 :=
  if 0 < ℓ then inv[ℓ.toNat - 1]?.getD idRows else loc[(-ℓ).toNat - 1]?.getD idRows

@[expose] def chkU (loc inv : Array (Array V2)) : Bool :=
  let T := uTab loc inv
  (List.range 11).all fun i =>
    eqRows (mulRows (T[i]?.getD idRows) (T[i]?.getD idRows)) idRows &&
      (List.range 11).all fun j =>
        eqRows (mulRows (T[i]?.getD idRows) (T[j]?.getD idRows))
          (mulRows (T[j]?.getD idRows) (T[i]?.getD idRows))

@[expose] def chkConj (loc inv : Array (Array V2)) : Bool :=
  let T := uTab loc inv
  letters.all fun ℓ =>
    (List.range 11).all fun j =>
      eqRows (mulRows (mulRows (xRows loc inv ℓ) (T[j]?.getD idRows)) (xiRows loc inv ℓ))
        (etaRows T 11 (letterRow ℓ j))

@[expose] def w0 : V2 := ⟨UInt64.ofNat w0Lo, UInt64.ofNat w0Hi⟩

@[expose] def differs (a b : V2) : Bool := (List.range 112).any fun j => a.testBit j != b.testBit j

@[expose] def etaVec (F : Array (Array V2)) (n c : Nat) : V2 :=
  (List.range n).foldl (fun acc j => if c.testBit j then frApply (F[j]?.getD #[]) acc else acc) w0

@[expose] def xpRows (loc inv : Array (Array V2)) : Array V2 := wordRows loc inv xpWord

@[expose] def chkFree (loc inv : Array (Array V2)) : Bool :=
  let F := (uTab loc inv).map frTable
  (List.range 2048).all fun c => c == 0 || differs (etaVec F 11 c) w0

@[expose] def chkOut (loc inv : Array (Array V2)) : Bool :=
  let F := (uTab loc inv).map frTable
  let y := frApply (frTable (xpRows loc inv)) w0
  (List.range 2048).all fun c => differs (etaVec F 11 c) y

@[expose] def chkFus (loc inv : Array (Array V2)) : Bool :=
  let T := uTab loc inv
  let xp := xpRows loc inv
  let s := mulRows (mulRows rowsA (T[0]?.getD idRows)) rowsA
  eqRows (mulRows xp xp) idRows && eqRows (powRows (mulRows s xp) 33) idRows

end CFSG.Sporadic.J4.QT

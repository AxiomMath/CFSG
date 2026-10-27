module

public import Certificates.Data.Kernel.SporLatDc
public import Certificates.Data.CFSGNative.SporLat.Code

public section

namespace CFSG.KC.SLDc

open CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def pairF (n : Nat) (f : Nat → Nat) (p : Nat) : Nat :=
  Nat.add (f (Nat.mod p n)) (Nat.mul n (f (Nat.div p n)))

@[expose] def tabF (t : List Nat) (p : Nat) : Nat := t.getD p 0

@[expose] def codeAT (n : Nat) (t : Array Nat) (c : Nat) : Nat :=
  encodeSet n (insN ((decodeSet n c c).map fun p => t.getD p 0))

@[expose] def codeSetT (n : Nat) (t : Array Nat) (x : List Nat) : List Nat :=
  insN (x.map (codeAT n t))

@[expose] def wordTabL (tabs : Array (Array Nat)) (n : Nat) (w : List Nat) : Array Nat :=
  ((List.range n).map (wordImg tabs w)).toArray

@[expose] def omL {Lab : Type} (x : List Lab × List (List Nat) × List Nat × List Nat) :
    OmegaData Lab :=
  ⟨x.1.toArray, (x.2.1.map List.toArray).toArray, x.2.2.1.toArray, x.2.2.2.toArray⟩

@[expose] def omCodeOK (n : Nat) (ts : Array (Array Nat)) (x0 : List Nat)
    (O : OmegaData (List Nat)) : Bool :=
  omOKG (fun l x => codeSetT n (ts.getD l #[]) x) x0 ts.size O

end CFSG.KC.SLDc

end

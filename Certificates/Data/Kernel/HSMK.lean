module

public import Certificates.Data.Kernel.WEMK

public section

namespace Certificates.HSMK

open Certificates.WEMK Certificates.TWLK

@[expose] def npowN (n : Nat) (A : NMat) : Nat → NMat
  | 0 => idN n
  | k + 1 => nmul n (npowN n A k) A

@[expose] def kRel (n : Nat) (T : List NMat) (E : List (List Nat)) : Bool :=
  (List.range T.length).all fun i => (List.range T.length).all fun j =>
    isOneN n (npowN n (nmul n (T.getD i []) (T.getD j [])) ((E.getD i []).getD j 0))

@[expose] def kExtra (n : Nat) (T : List NMat) : Bool :=
  isOneN n (npowN n (nmul n (nmul n (nmul n (T.getD 2 []) (T.getD 1 [])) (T.getD 2 [])) (T.getD 3 [])) 3)

@[expose] def kGen (n : Nat) (T : List NMat) (V : List KPair) (tab : List (List Nat)) (par : List (Nat × Nat)) :
    Bool :=
  T.all (wfM n) && T.all (fun s => isOneN n (nmul n s s)) && decide (0 < V.length) &&
  decide (mat n (V.getD 0 kP0) = T.getD 0 []) && kTab n T V tab && kPar T V tab par

@[expose] def wfV (n : Nat) (v : List Nat) : Bool := decide (v.length = n) && v.all fun x => decide (x < 13)

@[expose] def pword (n : Nat) (G : List KPair) (v : List Nat) (w : List Nat) : List Nat :=
  w.foldl (fun u g => nmv (mat n (G.getD g kP0)) u) v

@[expose] def kOrb (n : Nat) (G : List KPair) : List Nat → List (List Nat × List Nat) → Bool
  | _, [] => true
  | u, r :: rs => (r.1.all fun g => decide (g < G.length)) && wfV n r.2 && decide (pword n G u r.1 = r.2) &&
      kOrb n G r.2 rs

@[expose] def kLev (n : Nat) (G : List KPair) (b : List Nat) (R : List (List Nat × List Nat)) : Bool :=
  wfV n b && kOrb n G b R && kIncr (R.map fun r => kVKey 13 [r.2])

@[expose] def kSub (n : Nat) (G G' : List KPair) (b : List Nat) : Bool :=
  G'.all fun q => G.any (fun p => decide (p = q)) && decide (nmv (mat n q) b = b)

@[expose] def kChain (n : Nat) : List KPair → List (List Nat × (List (List Nat × List Nat) × List KPair)) → Bool
  | _, [] => true
  | G, l :: ls => kLev n G l.1 l.2.1 && kSub n G l.2.2 l.1 && kChain n l.2.2 ls

end Certificates.HSMK

end

module

public import Certificates.Data.Kernel.SporLatOm
public import Certificates.Data.CFSGNative.SporLat.Code

public section

namespace CFSG.KC.SLOm

open CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def codeActF (n : Nat) (f : Nat → Nat) (c : Nat) : Nat :=
  encodeSet n (insN ((decodeSet n c c).map f))

@[expose] def omOKC (n : Nat) (Δ : List Nat) (L : Nat → Nat → Nat) (nl : Nat)
    (O : OmegaData (List Nat)) : Bool :=
  O.lbl[0]! == Δ && decide (0 < O.lbl.size) &&
    (List.range nl).all (fun l => (List.range O.lbl.size).all fun i =>
      decide ((O.pn[l]!)[i]! < O.lbl.size) &&
        O.lbl[(O.pn[l]!)[i]!]! == insN (O.lbl[i]!.map (codeActF n (L l)))) &&
    (List.range O.lbl.size).all (fun i => i == 0 ||
      (decide (O.par[i]! < i) && decide (O.via[i]! < nl) && (O.pn[O.via[i]!]!)[O.par[i]!]! == i)) &&
    decide O.lbl.toList.Nodup

@[expose] def orbOKC (n : Nat) (Δ : List Nat) (L : Nat → Nat → Nat) (nl m : Nat) (x : Nat → Nat)
    (R : Option (OmegaData (List Nat) × Bool)) : Bool :=
  match R with
  | some R => omOKC n Δ L nl R.1 && R.1.lbl.size == m &&
      R.1.lbl.toList.all fun lb => insN (lb.map (codeActF n x)) == lb
  | none => false

@[expose] def rChkC (n : Nat) (Δ : List Nat) (L : Nat → Nat → Nat) (ns : Nat)
    (AB : Nat → Nat → Nat) (z : Nat → Nat) (uWords : List (List Nat)) (yw nw : List Nat)
    (r m fuel : Nat) : Bool :=
  uWords.all (fun w => w.all fun l => decide (l < 2)) &&
    yw.all (fun l => decide (l < ns + uWords.length)) && nw.all (fun l => decide (l < ns)) &&
    decide (0 < n) &&
    (List.range uWords.length).all (fun k => (List.range n).all fun p =>
      L (ns + k) p == wordF AB (uWords.getD k []) p) &&
    orbOKC n Δ L (ns + uWords.length) m (wordF L nw)
      (omTwin (fun l lb => insN (lb.map (codeActF n (L l)))) (ns + uWords.length) Δ (m + 1)
        fuel) &&
    (List.range uWords.length).all (fun k => (List.range n).all fun p =>
      L (ns + k) (z p) == z (L (ns + k) p)) &&
    (List.range n).all (fun p => wordF (fun _ => wordF L yw) (List.replicate r 0) p == p) &&
    !(List.range n).all (fun p => wordF L yw p == p) &&
    (List.range n).all (fun p => wordF L yw (z p) == z (wordF L yw p)) &&
    !(List.range n).all (fun p => wordF L yw (wordF L nw p) == wordF L nw (wordF L yw p))

end CFSG.KC.SLOm

end

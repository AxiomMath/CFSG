module

public import Certificates.Data.Kernel.M24G.Dual

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

@[expose] def discsOvalsT (LU : List Nat) (tr : Nat → Nat × Nat × Nat) : List (List Nat) :=
  let discs := LU.map fun d => LU.filter fun k => k != d && Native.meets (tr d) (tr k)
  let fives := Native.combs 5 LU
  let ovals := fives.filter fun D => D.all fun d => D.all fun k =>
    d == k || !(Native.meets (tr d) (tr k))
  discs ++ ovals

@[expose] def tabRow (LU : List Nat) (RU : List (List Nat)) (a : Nat) : List Nat :=
  ((LU.zip RU).lookup a).getD []

@[expose] def c311A (DS : List (List Nat)) (row : Nat → List Nat) (tr : Nat → Nat × Nat × Nat)
    (x : (Nat × Nat × Nat) × List Nat) : Bool :=
  DS.all fun D => D.any fun d =>
    x.2.any (fun q => (row d).contains q) || Native.zc x.1 (tr d) == 1

@[expose] def rowMask (r : List Nat) : Nat := r.foldr (fun q a => 2 ^ q ||| a) 0

@[expose] def orRows (TS : List (List Nat)) (N : List Nat) : Nat :=
  N.foldr (fun k a => rowMask (TS.getD k []) ||| a) 0

@[expose] def nbOK (TS : List (List Nat)) (d : Nat) (N : List Nat) (M : Nat) : Bool :=
  N.all (fun k => decide (k < 3795) &&
    (k == d || (TS.getD d []).any fun q => (TS.getD k []).contains q)) && orRows TS N == M

@[expose] def nbsOK (TS : List (List Nat)) (LU : List Nat) (NB : List (List Nat))
    (MS : List Nat) : Bool :=
  (LU.zip (NB.zip MS)).all fun x => nbOK TS x.1 x.2.1 x.2.2

@[expose] def tabNM (LU : List Nat) (NB : List (List Nat)) (MS : List Nat) (a : Nat) :
    List Nat × Nat :=
  ((LU.zip (NB.zip MS)).lookup a).getD ([], 0)

@[expose] def c311B (DS : List (List Nat)) (mask : Nat → Nat) : Bool :=
  DS.all fun D => D.foldr (fun d a => mask d ||| a) 0 == 2 ^ 1771 - 1

end CFSG.KC.M24G

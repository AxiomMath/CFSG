module

public import Certificates.Kernel.Co2Jc.NoZ4Data
public import Certificates.Data.Kernel.Co1F2

public section

namespace CertificateChecks.KernelCo2Jc

open CFSG.KC.Enum CFSG.Sporadic.Co2Jc.Data

@[expose] def wOf (t : Nat) : List Nat := if t = 0 then rels[1]! else rels[9]!

@[expose] def GK (k : Nat) : Nat :=
  (List.range 10).foldl (fun acc j =>
    acc ||| ((List.range 10).foldl (fun s i =>
      if ((CFSG.Sporadic.Co2Smith.Native.glNJTab[k]!).getD i 0).testBit j then s ||| 2 ^ i
      else s) 0) * 2 ^ (10 * j)) 0

@[expose] def CS (r : Nat) : Nat :=
  noZ4Sel.foldl (fun acc p => if p.1 = r then acc ||| 2 ^ (10 * p.2.1 + p.2.2) else acc) 0

@[expose] noncomputable def PR (t i : Nat) : Nat :=
  pg (nat_lit 100) (nat_lit 1267650600228229401496703205375) (NZ (2 * t)) i

@[expose] noncomputable def SF (t i : Nat) : Nat :=
  pg (nat_lit 100) (nat_lit 1267650600228229401496703205375) (NZ (2 * t + 1)) i

@[expose] noncomputable def termK (r t i : Nat) : Nat :=
  CFSG.KC.M1F2.mulF 10 (CFSG.KC.M1F2.mulF 10 (CFSG.KC.Co1F2.trK 10 (PR t i)) (CS r))
    (CFSG.KC.Co1F2.trK 10 (SF t (i + 1)))

@[expose] noncomputable def coeffT (k r t : Nat) : Nat :=
  (List.range (wOf t).length).foldl (fun acc i =>
    if (wOf t)[i]! = k then acc ^^^ termK r t i else acc) 0

@[expose] noncomputable def coeffK (k : Nat) : Nat := coeffT k 1 0 ^^^ (coeffT k 9 1 ^^^ 0)

@[expose] def eL (A : List (List Nat)) (i j : Nat) : Nat := (A.getD i []).getD j 0

@[expose] def mul4 (A B : List (List Nat)) : List (List Nat) :=
  (List.range 10).map fun i => (List.range 10).map fun j =>
    ((List.range 10).map fun k => eL A i k * eL B k j).sum % 4

@[expose] def id4 : List (List Nat) :=
  (List.range 10).map fun i => (List.range 10).map fun j => if i = j then 1 else 0

@[expose] def G4L (k : Nat) : List (List Nat) :=
  (List.range 10).map fun j => (List.range 10).map fun i =>
    if ((CFSG.Sporadic.Co2Smith.Native.glNJTab[k]!).getD i 0).testBit j then 1 else 0

@[expose] def P4 (w : List Nat) : List (List Nat) := w.foldr (fun k acc => mul4 (G4L k) acc) id4

@[expose] noncomputable def QL (t : Nat) : List (List Nat) :=
  (List.range 10).map fun i => (List.range 10).map fun j => pg (nat_lit 2) (nat_lit 3) (NQ t) (10 * i + j)

@[expose] noncomputable def qE (r a b : Nat) : ZMod 4 :=
  (pg (nat_lit 2) (nat_lit 3) (NQ (if r = 1 then 0 else 1)) (10 * (a % 10) + b % 10) : ZMod 4)

end CertificateChecks.KernelCo2Jc

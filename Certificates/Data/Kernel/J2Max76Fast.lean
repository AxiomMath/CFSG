module

public import Certificates.Data.Kernel.J2Max76

public section

namespace CFSG.KC.J2Max76

open Certificates.K76J2Max Certificates.G2ThreeMax CFSG.Monster.B.TwoA.Census

@[expose] noncomputable def forceJ (y : ℕ) (k : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def imgW (n : ℕ) (l : List ℕ) : ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun t _ ih i acc => forceJ (Nat.succ i) fun j =>
      forceJ (Bool.rec (motive := fun _ => ℕ) acc (Nat.lor acc (Nat.shiftLeft (nat_lit 1) t))
        (Nat.blt (nat_lit 0) (Nat.land n (Nat.shiftLeft (nat_lit 1) i)))) fun a => ih j a) l

@[expose] noncomputable def nthJ (d : List ℕ) (L : List (List ℕ)) : ℕ → List ℕ :=
  List.rec (motive := fun _ => ℕ → List ℕ) (fun _ => d)
    (fun a _ ih k => Nat.rec (motive := fun _ => List ℕ) a (fun j _ => ih j) k) L

@[expose] noncomputable def actK (G : List (List ℕ)) (k n : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (act k n)
    (forceJ n fun m => imgW m (nthJ [] G k) (nat_lit 0) (nat_lit 0)) (Nat.blt k (nat_lit 5))

@[expose] noncomputable def gensOK (G : List (List ℕ)) : Bool :=
  (List.range 5).all fun k => nthJ [] G k == (gensArr[k]!).toList && (gensArr[k]!).size == 315

@[expose] def certEqB (c d : NatCert) : Bool :=
  c.pts.toList == d.pts.toList && c.edges.toList.map Array.toList == d.edges.toList.map Array.toList &&
    c.par.toList == d.par.toList && c.lab.toList == d.lab.toList

@[expose] def orbsEqB : List (ℕ × NatCert) → List (ℕ × NatCert) → Bool
  | [], [] => true
  | a :: as, b :: bs => a.1 == b.1 && certEqB a.2 b.2 && orbsEqB as bs
  | _, _ => false

@[expose] def repLitOK (c : NatCert) (hp : Array (Array ℕ)) (r : ℕ) (w : List ℕ) (rp : Array ℕ)
    (c₃ : NatCert) : Bool :=
  w.all (· < 5) && applyW c w 0 == r &&
    natCertOK (repAct hp rp) 4 (fun u => decide (u < 280)) 0 c₃ &&
    c₃.pts.toList.mergeSort (fun a b => decide (a ≤ b)) == List.range 280

end CFSG.KC.J2Max76

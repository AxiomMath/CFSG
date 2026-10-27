module

public import Certificates.Data.Kernel.J2Max76Fast

public section

namespace CFSG.KC.J2Max76

open Certificates.K76J2Max Certificates.G2ThreeMax CFSG.Monster.B.TwoA.Census CFSG.KC.Bfs

@[expose] def lane (PK W j : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight PK (Nat.mul W j)) (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1))

@[expose] noncomputable def pin1 (W : ℕ) (L : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun PK => Nat.beq PK (nat_lit 0))
    (fun a _ ih PK => Bool.rec (motive := fun _ => Bool) false (ih (Nat.shiftRight PK W))
      (Nat.beq (Nat.land PK (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1))) a)) L

@[expose] def rdT (PK W m i k : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (nat_lit 0) (lane PK W (Nat.add (Nat.mul m i) k)) (Nat.blt k m)

@[expose] noncomputable def pinT(PK W m : ℕ) (rows : List (List ℕ)) : Bool :=
  rows.all (fun r => r.length == m) && pin1 W rows.flatten PK

@[expose] def rszR (n m i : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (nat_lit 0) m (Nat.blt i n)

@[expose] def natPointR (act : ℕ → ℕ → ℕ) (ngen : ℕ) (valid : ℕ → Bool) (n : ℕ) (P : ℕ → ℕ)
    (E : ℕ → ℕ → ℕ) (R par lab : ℕ → ℕ) (i : ℕ) : Bool :=
  valid (P i) && R i == ngen &&
    (List.range ngen).all (fun k => decide (E i k < n) && P (E i k) == act k (P i)) &&
    (i == 0 || (decide (par i < i) && decide (lab i < ngen) && P i == act (lab i) (P (par i))))

@[expose] def natCertR (act : ℕ → ℕ → ℕ) (ngen : ℕ) (valid : ℕ → Bool) (root n : ℕ)
    (P : ℕ → ℕ) (E : ℕ → ℕ → ℕ) (R par lab : ℕ → ℕ) (L : List ℕ) : Bool :=
  decide (0 < n) && P 0 == root &&
    (List.range n).all (natPointR act ngen valid n P E R par lab) &&
    (L.insertionSort (· ≤ ·)).Pairwise (· < ·)

@[expose] noncomputable def certPin(c : NatCert) (n W m PKp PKe PKpar PKlab : ℕ) : Bool :=
  c.pts.size == n && c.edges.size == n && pin1 W c.pts.toList PKp &&
    pinT PKe 9 m (c.edges.toList.map Array.toList) && pin1 9 c.par.toList PKpar &&
    pin1 9 c.lab.toList PKlab

@[expose] def natCertP (act : ℕ → ℕ → ℕ) (ngen : ℕ) (valid : ℕ → Bool) (root n W m PKp PKe PKpar
    PKlab : ℕ) (L : List ℕ) : Bool :=
  natCertR act ngen valid root n (lane PKp W) (rdT PKe 9 m) (rszR n m) (lane PKpar 9)
    (lane PKlab 9) L

@[expose] def hR (PKh s i : ℕ) : ℕ := rdT PKh 9 280 s i

@[expose] def repR (PKh PKrp s i : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lane PKrp 9 i) (rdT PKh 9 280 s i) (Nat.blt s 3)

@[expose] def permL (T : ℕ → ℕ → ℕ) (n : ℕ) (w : List ℕ) : List ℕ :=
  (List.range n).map fun i => w.foldr (fun k j => T k j) i

@[expose] def tabR (PKe k i : ℕ) : ℕ := rdT PKe 9 5 i k

@[expose] def repLitP (c : NatCert) (PKh : ℕ) (r : ℕ) (w : List ℕ) (PKrp : ℕ) (PKp PKe PKpar
    PKlab : ℕ) (L : List ℕ) : Bool :=
  w.all (· < 5) && applyW c w 0 == r &&
    natCertP (repR PKh PKrp) 4 (fun u => decide (u < 280)) 0 280 9 4 PKp PKe PKpar PKlab L &&
    L.insertionSort (· ≤ ·) == List.range 280

end CFSG.KC.J2Max76

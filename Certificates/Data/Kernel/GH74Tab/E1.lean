
module

public import Certificates.Data.Kernel.GH74Tab.Defs
public import CFSG.GH74.GLS.C3.Layer2.L4ModelE1

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

variable (D : Dat)

@[expose] def vIK (a : Nat) : Nat := mul D D.x0 (g6 a D.x0)

@[expose] def eLK (a : Nat) : List Nat :=
  let X := reachK D a 12 (1 <<< D.x0)
  let v := vIK D a
  r64.filter fun i => i == D.one || i == v ||
    (bit D.IV i && bit X i && mul D i v == mul D v i && bit X (mul D i v))

@[expose] def e1K0 : Bool :=
  (r64.all fun i => r64.all fun j =>
    !(bit D.IV i && bit D.IV j && mul D i j == mul D j i && i != j) || bit D.IV (mul D i j)) &&
  bit D.IV D.x0 && r64.all fun i => mul D D.x0 i == mul D i D.x0

@[expose] def e1K1 (n : ℕ) [NeZero n] (a : Nat) : Bool :=
  let v := vIK D a
  let L := eLK D a
  bit D.IV v && decide ((mkTab n).el.get (f64 v) = vStdE1 n) &&
  (L.all fun i => L.all fun j => L.contains (mul D i j) && mul D i j == mul D j i) &&
  (L.all fun i => mul D i i == D.one) && L.length == 8 &&
  (r64.all fun s => L.all fun i => L.contains (mul D (mul D s i) (g6 D.I s))) &&
  L.all fun i => L.contains (g6 a i)

@[expose] def e1K2 (a : Nat) : Bool :=
  let X := reachK D a 12 (1 <<< D.x0)
  let V := reachK D a 12 (1 <<< vIK D a)
  let S := r64.filter fun i => bit D.IV i && bit V i && bit X (mul D D.x0 i)
  S.all fun i => g6 D.C i == g6 D.C (S.headD 0)

@[expose] def e1K3 (n : ℕ) [NeZero n] (a : Nat) : Bool :=
  let L := eLK D a
  let el := fun i : Nat => (mkTab n).el.get (f64 i)
  (repListE1 n).all fun r => L.all fun i => L.any fun j => decide (el j = r * el i * r⁻¹)

@[expose] def e1OK (n : ℕ) [NeZero n] (L : List (Nat × Nat)) : Bool :=
  e1K0 D && L.all fun p => e1K1 D n p.1 && e1K2 D p.1 && e1K3 D n p.1

end CFSG.KC.GH74Tab

end

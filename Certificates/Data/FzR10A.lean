module

public import Certificates.Data.FzR10

public section

namespace Certificates.FzR10A

open Certificates.FzR10

structure Mat where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving DecidableEq

@[expose] def Mat.ap (m : Mat) (p : Nat) : Nat :=
  (m.a * (p % 8) + m.b * (p / 8 % 8)) % 8 + 8 * ((m.c * (p % 8) + m.d * (p / 8 % 8)) % 8)

@[expose] def Mat.mul (m n : Mat) : Mat :=
  ⟨(m.a * n.a + m.b * n.c) % 8, (m.a * n.b + m.b * n.d) % 8,
    (m.c * n.a + m.d * n.c) % 8, (m.c * n.b + m.d * n.d) % 8⟩

@[expose] def Mat.one : Mat := ⟨1, 0, 0, 1⟩

@[expose] def allMats : List Mat :=
  (List.range 8).flatMap fun a => (List.range 8).flatMap fun b =>
    (List.range 8).flatMap fun c => (List.range 8).map fun d => ⟨a, b, c, d⟩

@[expose] def addP (p q : Nat) : Nat :=
  (p % 8 + q % 8) % 8 + 8 * ((p / 8 % 8 + q / 8 % 8) % 8)

@[expose] def subP (p q : Nat) : Nat :=
  (p % 8 + 8 - q % 8) % 8 + 8 * ((p / 8 % 8 + 8 - q / 8 % 8) % 8)

@[expose] def inZ (p : Nat) : Bool := p % 8 % 4 == 0 && p / 8 % 8 % 4 == 0

@[expose] def fixP (m : Mat) : List Nat := (List.range 64).filter fun p => m.ap p == p

@[expose] def rho0 : Mat := ⟨0, 7, 1, 7⟩

@[expose] def candT (m : Mat) : Bool :=
  m.mul m == Mat.one && m.mul rho0 == rho0.mul m && (fixP m).length == 16 &&
    (fixP m).all (fun p => p % 2 == 0 && p / 8 % 2 == 0) &&
    (List.range 64).all fun p => inZ (subP (m.ap p) p)

@[expose] def candS (t m : Mat) : Bool :=
  m.mul m == Mat.one && m.mul rho0 == rho0.mul m && m.mul t == t.mul m && !(m == Mat.one) &&
    (fixP t).all (fun p => m.ap p == subP 0 p) &&
    (List.range 64).all fun p => (fixP t).contains (subP (m.ap p) p)

@[expose] def candL (t m : Mat) : Bool :=
  m.mul m == Mat.one && m.mul rho0 == (rho0.mul rho0).mul m && m.mul t == t.mul m &&
    (List.range 64).any (fun p => inZ p && m.ap p != p) &&
    (List.range 64).any fun p => t.ap (subP (m.ap p) p) != subP (m.ap p) p

@[expose] def vAct (t s l : Mat) (v q : Nat) : Nat :=
  let q1 := if v / 4 % 2 == 1 then l.ap q else q
  let q2 := if v / 2 % 2 == 1 then s.ap q1 else q1
  if v % 2 == 1 then t.ap q2 else q2

@[expose] def emA (t s l : Mat) (n m : Nat) : Nat :=
  let v := n / 64 % 8
  addP (n % 64) (vAct t s l v (m % 64)) + 64 * (v ^^^ (m / 64 % 8))

@[expose] def parOfA (t s l : Mat) : Par where
  e := emA t s l
  tI := 64
  sI := 128
  inTL := fun x => t.ap (x % 64) == x % 64 && x / 64 % 4 == 0
  inW := fun x => t.ap (x % 64) == x % 64 && x / 64 < 2
  inTZ := fun x => x / 64 == 1 && inZ (x % 64)
  rhoMap := fun x => rho0.ap (x % 64) + 64 * (x / 64)
  gens := #[1, 8, 64, 128, 256]

@[expose] def fusionLoopA (_ : Unit := ()) : Bool :=
  (allMats.filter candT).all fun t =>
    let ls := allMats.filter (candL t)
    (allMats.filter (candS t)).all fun s =>
      (ls.filter fun l => s.mul l == l.mul s).all fun l => fusionBad (parOfA t s l)

end Certificates.FzR10A

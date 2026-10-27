module

public import Certificates.Data.CFSGNative.SectionRank.Local

public section

namespace CFSG.SectionRank.Native

set_option compiler.extract_closed false

namespace Co1Gen

structure NormEl where
  reg : Nat
  ord : Nat

structure Plane where
  u : Nat
  v : Nat
  t : Nat
  norms : List NormEl

structure Data where
  seedA : String
  seedB : String
  nregs : Nat
  prog : List Op
  fuelP : Nat
  plane1 : Plane
  plane2 : Plane
  nregs2 : Nat
  prog2 : List Op
  rA : Nat
  rB : Nat

end Co1Gen

namespace Ops

variable {M V : Type} (O : Ops M V)

@[expose] def co1GenStep (gens xs : List M) : List M :=
  (xs.flatMap fun x => gens.map (O.mul x)).foldl
    (fun acc y => if acc.any (O.eq y) then acc else acc ++ [y]) xs

@[expose] def co1GenAux (gens : List M) : Nat → List M → List M
  | 0, xs => xs
  | n + 1, xs => if (O.co1GenStep gens xs).length = xs.length then xs else co1GenAux gens n (O.co1GenStep gens xs)

@[expose] def co1GenClosure (gens : List M) (fuel : Nat) : List M := O.co1GenAux gens fuel [O.one]

@[expose] def co1GenClosed (gens xs : List M) : Bool :=
  xs.all fun x => gens.all fun g => xs.any (O.eq (O.mul x g))

@[expose] def co1GenPlane [Inhabited M] [Inhabited V] (nregs : Nat) (R : Array M) (Pl : Co1Gen.Plane) :
    Bool :=
  decide (Pl.u < nregs) && decide (Pl.v < nregs) && O.eq (O.pow R[Pl.u]! 5) O.one &&
    O.eq (O.pow R[Pl.v]! 5) O.one && O.commOK R[Pl.u]! R[Pl.v]! &&
    O.normalFormOK 5 [R[Pl.u]!, R[Pl.v]!] Pl.t &&
    Pl.norms.all fun n =>
      decide (n.reg < nregs) && decide (0 < n.ord) && O.eq (O.pow R[n.reg]! n.ord) O.one &&
        [R[Pl.u]!, R[Pl.v]!].all fun s =>
          (List.range 5).any fun a => (List.range 5).any fun b =>
            O.conjOK R[n.reg]! s (O.mul (O.pow R[Pl.u]! a) (O.pow R[Pl.v]! b))

@[expose] def co1GenCheck [Inhabited M] [Inhabited V] (D : Co1Gen.Data) : Bool :=
  let A0 := O.decode D.seedA
  let B0 := O.decode D.seedB
  let R := O.regsOf D.seedA D.seedB D.nregs D.prog
  let pg := [R[D.plane1.u]!, R[D.plane1.v]!, R[D.plane2.u]!, R[D.plane2.v]!]
  let xs := O.co1GenClosure pg D.fuelP
  let ns := (D.plane1.norms ++ D.plane2.norms).map fun n => R[n.reg]!
  let R2 := O.run D.prog2 (Array.ofFn (n := D.nregs2) fun r => (ns[r.val]?).getD O.one)
  decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
    O.eq (O.pow A0 2) O.one && O.eq (O.pow B0 3) O.one &&
    pg.all (fun x => O.eq (O.pow x 5) O.one) && O.co1GenClosed pg xs &&
    xs.all (fun x => O.eq (O.pow x 625) O.one) &&
    O.co1GenPlane D.nregs R D.plane1 && O.co1GenPlane D.nregs R D.plane2 &&
    decide (ns.length ≤ D.nregs2) && D.prog2.all (Op.lt D.nregs2) &&
    decide (D.rA < D.nregs2) && decide (D.rB < D.nregs2) &&
    O.eq R2[D.rA]! A0 && O.eq R2[D.rB]! B0

end Ops

end CFSG.SectionRank.Native

module

public import Certificates.Data.Kernel.OpsF2KSq
public import Certificates.Data.Co1Gen

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native CFSG.SectionRank.Native.Co1Gen

@[expose] noncomputable def closStepK (d : Nat) (gens xs : List Nat) : List Nat :=
  (xs.flatMap fun x => gens.map (mulF d x)).foldl
    (fun acc y => if acc.any (Nat.beq y) then acc else acc ++ [y]) xs

@[expose] noncomputable def closAuxK (d : Nat) (gens : List Nat) : Nat → List Nat → List Nat
  | 0, xs => xs
  | n + 1, xs =>
    let ys := closStepK d gens xs
    if ys.length = xs.length then xs else closAuxK d gens n ys

@[expose] noncomputable def planeK (d nregs : Nat) (R : List Nat) (Pl : Plane) : Bool :=
  let U := getR d R Pl.u
  let V := getR d R Pl.v
  decide (Pl.u < nregs) && decide (Pl.v < nregs) && decide (Pl.t < d) &&
    Nat.beq (powK d U 5) (idF d) && Nat.beq (powK d V 5) (idF d) && commK d U V &&
    distinctK ((List.range (5 ^ 2)).map fun n => appBaseK d 5 [U, V] n (pw2 Pl.t)) &&
    Pl.norms.all fun n =>
      decide (n.reg < nregs) && decide (0 < n.ord) && decide (n.ord < 65536) &&
        Nat.beq (powK d (getR d R n.reg) n.ord) (idF d) &&
        [U, V].all fun s =>
          (List.range 5).any fun a => (List.range 5).any fun b =>
            conjK d (getR d R n.reg) s (mulF d (powK d U a) (powK d V b))

@[expose] noncomputable def co1GenK (d A B : Nat) (D : Co1Gen.Data) : Bool :=
  let R := runK d A B D.nregs D.prog
  let pg := [getR d R D.plane1.u, getR d R D.plane1.v, getR d R D.plane2.u, getR d R D.plane2.v]
  let xs := closAuxK d pg D.fuelP [idF d]
  let ns := (D.plane1.norms ++ D.plane2.norms).map fun n => getR d R n.reg
  let R2 := D.prog2.foldl (stepK d) ((List.range D.nregs2).map fun r => ns.getD r (idF d))
  seedsOK d A B && D.prog.all expOK && D.prog2.all expOK && decide (2 ≤ D.nregs) &&
    D.prog.all (Op.lt D.nregs) &&
    Nat.beq (powK d A 2) (idF d) && Nat.beq (powK d B 3) (idF d) &&
    pg.all (fun x => Nat.beq (powK d x 5) (idF d)) &&
    xs.all (fun x => pg.all fun g => xs.any (Nat.beq (mulF d x g))) &&
    xs.all (fun x => Nat.beq (powK d x 625) (idF d)) &&
    planeK d D.nregs R D.plane1 && planeK d D.nregs R D.plane2 &&
    decide (ns.length ≤ D.nregs2) && D.prog2.all (Op.lt D.nregs2) &&
    decide (D.rA < D.nregs2) && decide (D.rB < D.nregs2) &&
    Nat.beq (getR d R2 D.rA) A && Nat.beq (getR d R2 D.rB) B

end CFSG.KC.OpsF2K

end

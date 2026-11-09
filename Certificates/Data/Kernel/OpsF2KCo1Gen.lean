module

public import Certificates.Data.Kernel.OpsF2KSq
public import Certificates.Data.Co1Gen

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native CFSG.SectionRank.Native.Co1Gen

@[expose] noncomputable def co1SpanK (d : Nat) : List Nat → List Nat
  | [] => [idF d]
  | g :: gs => (co1SpanK d gs).flatMap fun x => (List.range 5).map fun a => mulF d x (powK d g a)

@[expose] noncomputable def co1PCK (d : Nat) : List Nat → Bool
  | [] => true
  | g :: gs => Nat.beq (powK d g 5) (idF d) &&
      gs.all (fun h => (co1SpanK d gs).any (conjK d g h)) && co1PCK d gs

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
  let U1 := getR d R D.plane1.u
  let V1 := getR d R D.plane1.v
  let U2 := getR d R D.plane2.u
  let C := mulF d (mulF d U1 U2) (mulF d (powK d U1 4) (powK d U2 4))
  let ns := (D.plane1.norms ++ D.plane2.norms).map fun n => getR d R n.reg
  let R2 := D.prog2.foldl (stepK d) ((List.range D.nregs2).map fun r => ns.getD r (idF d))
  seedsOK d A B && D.prog.all expOK && D.prog2.all expOK && decide (2 ≤ D.nregs) &&
    D.prog.all (Op.lt D.nregs) &&
    Nat.beq (powK d A 2) (idF d) && Nat.beq (powK d B 3) (idF d) &&
    co1PCK d [U2, U1, C, V1] && (co1SpanK d [U1, V1]).any (Nat.beq (getR d R D.plane2.v)) &&
    planeK d D.nregs R D.plane1 && planeK d D.nregs R D.plane2 &&
    decide (ns.length ≤ D.nregs2) && D.prog2.all (Op.lt D.nregs2) &&
    decide (D.rA < D.nregs2) && decide (D.rB < D.nregs2) &&
    Nat.beq (getR d R2 D.rA) A && Nat.beq (getR d R2 D.rB) B

@[expose] noncomputable def getDG (L : List Nat) (i e : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => e)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun n _ => ih n) i) L i

@[expose] noncomputable def setG (L : List Nat) (k v : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x xs ih k => Nat.rec (motive := fun _ => List Nat) (v :: xs) (fun n _ => x :: ih n) k) L k

@[expose] noncomputable def stepG (d : Nat) (R : List Nat) (o : Op) : List Nat :=
  Op.rec (motive := fun _ => List Nat)
    (fun i j k => setG R k (mulF d (getDG R i (idF d)) (getDG R j (idF d))))
    (fun e i k => setG R k (powK d (getDG R i (idF d)) e)) o

@[expose] noncomputable def runG (d : Nat) (prog : List Op) (R : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun R => R) (fun o _ ih R => ih (stepG d R o))
    prog R

@[expose] noncomputable def co1GenG (d A B : Nat) (D : Co1Gen.Data) : Bool :=
  let R := runG d D.prog
    ((List.range D.nregs).map fun r => if r = 0 then A else if r = 1 then B else idF d)
  let U1 := getDG R D.plane1.u (idF d)
  let V1 := getDG R D.plane1.v (idF d)
  let U2 := getDG R D.plane2.u (idF d)
  let C := mulF d (mulF d U1 U2) (mulF d (powK d U1 4) (powK d U2 4))
  let ns := (D.plane1.norms ++ D.plane2.norms).map fun n => getDG R n.reg (idF d)
  let R2 := runG d D.prog2 ((List.range D.nregs2).map fun r => ns.getD r (idF d))
  seedsOK d A B && D.prog.all expOK && D.prog2.all expOK && decide (2 ≤ D.nregs) &&
    D.prog.all (Op.lt D.nregs) &&
    Nat.beq (powK d A 2) (idF d) && Nat.beq (powK d B 3) (idF d) &&
    co1PCK d [U2, U1, C, V1] &&
    (co1SpanK d [U1, V1]).any (Nat.beq (getDG R D.plane2.v (idF d))) &&
    planeK d D.nregs R D.plane1 && planeK d D.nregs R D.plane2 &&
    decide (ns.length ≤ D.nregs2) && D.prog2.all (Op.lt D.nregs2) &&
    decide (D.rA < D.nregs2) && decide (D.rB < D.nregs2) &&
    Nat.beq (getDG R2 D.rA (idF d)) A && Nat.beq (getDG R2 D.rB (idF d)) B

theorem getDG_eq (e : Nat) : ∀ (L : List Nat) (i : Nat), getDG L i e = L.getD i e
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: L, i + 1 => by
    change getDG L i e = _
    rw [getDG_eq e L i, List.getD_cons_succ]

theorem setG_eq (v : Nat) : ∀ (L : List Nat) (k : Nat), setG L k v = L.set k v
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: L, k + 1 => by
    change x :: setG L k v = _
    rw [setG_eq v L k, List.set_cons_succ]

theorem stepG_eq (d : Nat) (R : List Nat) : ∀ o : Op, stepG d R o = stepK d R o
  | .mul i j k => by
    change setG R k (mulF d (getDG R i (idF d)) (getDG R j (idF d))) = _
    rw [setG_eq, getDG_eq, getDG_eq]
    rfl
  | .pow e i k => by
    change setG R k (powK d (getDG R i (idF d)) e) = _
    rw [setG_eq, getDG_eq]
    rfl

theorem runG_eq (d : Nat) : ∀ (prog : List Op) (R : List Nat), runG d prog R = prog.foldl (stepK d) R
  | [], _ => rfl
  | o :: prog, R => by
    change runG d prog (stepG d R o) = _
    rw [runG_eq d prog, stepG_eq, List.foldl_cons]

theorem co1GenG_eq (d A B : Nat) (D : Co1Gen.Data) : co1GenG d A B D = co1GenK d A B D := by
  simp only [co1GenG, co1GenK, runG_eq, getDG_eq, runK, getR]
  rfl

end CFSG.KC.OpsF2K

end

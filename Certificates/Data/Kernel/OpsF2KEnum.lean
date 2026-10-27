module

public import Certificates.Data.Kernel.OpsF2KSq
public import Certificates.Data.J3Comm

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native

@[expose] def findK (y : Nat) : List Nat → Nat → Option Nat
  | [], _ => none
  | z :: zs, i => if Nat.beq y z then some i else findK y zs (i + 1)

abbrev EnSt := List Nat × List Nat × List Nat × List (List Nat)

@[expose] noncomputable def enumGensK (d h X : Nat) :
    List Nat → Nat → List Nat × List Nat × List Nat × List Nat →
      List Nat × List Nat × List Nat × List Nat
  | [], _, s => s
  | G :: gs, g, (E, par, lab, row) =>
    let Y := mulF d X G
    match findK Y E 0 with
    | some j => enumGensK d h X gs (g + 1) (E, par, lab, row ++ [j])
    | none => enumGensK d h X gs (g + 1) (E ++ [Y], par ++ [h], lab ++ [g], row ++ [E.length])

@[expose] noncomputable def enumStepK (d : Nat) (gens : List Nat) (s : EnSt) (h : Nat) : EnSt :=
  if h < s.1.length then
    let r := enumGensK d h (s.1.getD h 0) gens 0 (s.1, s.2.1, s.2.2.1, [])
    (r.1, r.2.1, r.2.2.1, s.2.2.2 ++ [r.2.2.2])
  else s

@[expose] noncomputable def enumK (d : Nat) (gens : List Nat) (cap : Nat) : EnSt :=
  (List.range cap).foldl (enumStepK d gens) ([idF d], [0], [0], [])

@[expose] noncomputable def enumOKK (d : Nat) (gens : List Nat) (n t : Nat) (s : EnSt) : Bool :=
  let E := s.1
  let par := s.2.1
  let lab := s.2.2.1
  let cl := s.2.2.2
  E.length == n && par.length == n && lab.length == n && cl.length == n && decide (0 < n) &&
    Nat.beq (E.getD 0 0) (idF d) &&
    (List.range n).all (fun i => i == 0 || (decide (par.getD i 0 < i) &&
      decide (lab.getD i 0 < gens.length) &&
      Nat.beq (E.getD i 0) (mulF d (E.getD (par.getD i 0) 0) (gens.getD (lab.getD i 0) 0)))) &&
    (List.range n).all (fun i => (List.range gens.length).all fun g =>
      decide ((cl.getD i []).getD g 0 < n) &&
        Nat.beq (mulF d (E.getD i 0) (gens.getD g 0)) (E.getD ((cl.getD i []).getD g 0) 0)) &&
    distinctK (E.map fun X => vmF d X (pw2 t))

@[expose] def memK (E : List Nat) (X : Nat) : Bool := E.any (Nat.beq X)

@[expose] noncomputable def genFactsK (d : Nat) (D : SylowCentralData) (K1 K2 : Nat) : Bool :=
  decide (0 < D.ok1) && decide (0 < D.ok2) && decide (D.ok1 < 65536) && decide (D.ok2 < 65536) &&
    Nat.beq (powK d K1 D.ok1) (idF d) && Nat.beq (powK d K2 D.ok2) (idF d)

@[expose] def baseOK (d A B : Nat) (D : SylowCentralData) : Bool :=
  seedsOK d A B && D.prog.all expOK && decide (D.t < d) && decide (2 ≤ D.nregs) &&
    D.prog.all (Op.lt D.nregs) && D.regsLt

@[expose] noncomputable def sylowCentralK (d A B : Nat) (D : SylowCentralData) : Bool :=
  let R := runK d A B D.nregs D.prog
  let K1 := getR d R D.rk1
  let K2 := getR d R D.rk2
  let X := getR d R D.rx
  let Y := getR d R D.ry
  let En := enumK d [K1, K2] D.nP
  baseOK d A B D && genFactsK d D K1 K2 && enumOKK d [K1, K2] D.nP D.t En &&
    memK En.1 X && memK En.1 Y && Nat.beq (powK d X 3) (idF d) &&
    Nat.beq (powK d Y 3) (idF d) && commK d X Y &&
    distinctK ((List.range (3 ^ 2)).map fun n => appBaseK d 3 [X, Y] n (pw2 D.t)) &&
    commK d X K1 && commK d X K2 && commK d Y K1 && commK d Y K2

@[expose] noncomputable def commTripleK (d A B : Nat) (D : CommTripleData) : Bool :=
  let R := runK d A B D.base.nregs D.base.prog
  let K1 := getR d R D.base.rk1
  let K2 := getR d R D.base.rk2
  let En := enumK d [K1, K2] D.base.nP
  baseOK d A B D.base && genFactsK d D.base K1 K2 && enumOKK d [K1, K2] D.base.nP D.base.t En &&
    decide (9 < D.trip.length) &&
    D.trip.all (fun t => decide (t.1 < D.base.nregs) && decide (t.2.1 < D.base.nregs) &&
      decide (t.2.2 < D.base.nregs) && (t.2.2 == D.base.rk1 || t.2.2 == D.base.rk2) &&
      memK En.1 (getR d R t.2.1) && Nat.beq (powK d (getR d R t.1) 3) (idF d) &&
      Nat.beq (mulF d (getR d R t.1) (mulF d (getR d R t.2.2) (getR d R t.2.1)))
        (mulF d (getR d R t.2.1) (getR d R t.2.2))) &&
    distinctK (D.trip.map fun t => vmF d (getR d R t.1) (pw2 D.base.t))

end CFSG.KC.OpsF2K

end

module

public import Certificates.Data.Kernel.OpsF2K
public import Certificates.Data.Kernel.OpsLayK
public import Certificates.Data.CoverCenterThreeCover

public section

namespace CFSG.KC.CoverCK

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

@[expose] def mergeK : Nat → List Nat → List Nat → List Nat
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, x :: a, [] => x :: a
  | n + 1, x :: a, y :: b =>
    Bool.rec (motive := fun _ => List Nat) (y :: mergeK n (x :: a) b) (x :: mergeK n a (y :: b))
      (Nat.blt x y)

@[expose] def pairK (f : Nat) : List (List Nat) → List (List Nat)
  | a :: b :: l => mergeK f a b :: pairK f l
  | l => l

@[expose] def passK (f : Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, l => l
  | n + 1, l => passK f n (pairK f l)

@[expose] def msortK (ks : List Nat) : List Nat :=
  (passK ks.length (nat_lit 20) (ks.map fun k => [k])).flatten

@[expose] def sortedK : List Nat → Bool
  | x :: y :: l => Nat.blt x y && sortedK (y :: l)
  | _ => true

@[expose] def bitK (m g : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight m g) 1) 1

@[expose] def kidsK (act : Nat → Nat → Nat) (v m : Nat) : List Nat → Nat → List Nat
  | [], _ => []
  | G :: gs, g => Bool.rec (motive := fun _ => List Nat) (kidsK act v m gs (g + 1))
      (act v G :: kidsK act v m gs (g + 1)) (bitK m g)

@[expose] def bfsK (act : Nat → Nat → Nat) (gens : List Nat) :
    List Nat → List Nat → List Nat → List Nat → Option (List Nat)
  | [], [], [], out => some out.reverse
  | [], _, _, _ => none
  | _ :: _, [], [], _ => none
  | m :: ms, v :: f, b, out => bfsK act gens ms f (List.reverseAux (kidsK act v m gens 0) b) (v :: out)
  | m :: ms, [], b, out =>
    match b.reverse with
    | [] => none
    | v :: f => bfsK act gens ms f (List.reverseAux (kidsK act v m gens 0) []) (v :: out)

@[expose] def orbitK (act : Nat → Nat → Nat) (gens : List Nat) (u : Nat) (masks : List Nat) :
    Bool :=
  !masks.isEmpty && masks.all (fun m => Nat.blt m (2 ^ gens.length)) &&
    match bfsK act gens masks [u] [] [] with
    | some vs => sortedK (msortK vs)
    | none => false

@[expose] def bitsK (m : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, g => Bool.rec (motive := fun _ => List Nat) (bitsK m k (g + 1)) (g :: bitsK m k (g + 1))
      (bitK m g)

@[expose] def labOf (ng : Nat) (masks : List Nat) : List Nat :=
  0 :: masks.flatMap fun m => bitsK m ng 0

@[expose] def parOf (ng : Nat) (masks : List Nat) : List Nat :=
  0 :: (masks.zipIdx.flatMap fun p => (bitsK p.1 ng 0).map fun _ => p.2)

section F2

open CFSG.KC.OpsF2K

@[expose] noncomputable def evalWK2 {m : Nat} (d : Nat) (G I : List Nat) :
    List (Fin m × Bool) → Nat
  | [] => idF d
  | x :: w => mulF d (if x.2 then G.getD x.1.val 0 else I.getD x.1.val 0) (evalWK2 d G I w)

@[expose] def dataOK2 {m : Nat} (d A B : Nat) (D : CoverData m) : Bool :=
  seedsOK d A B && D.prog.all expOK && decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
    decide (D.gens.length = m) && decide (D.invExp.length = m) &&
    D.gens.all (fun r => decide (r < D.nregs)) && D.invExp.all (fun e => decide (e < 65536))

@[expose] noncomputable def coverK2 {m : Nat} (d A B : Nat) (D : CoverData m) : Bool :=
  let R := runK d A B D.nregs D.prog
  let G := D.gens.map (getR d R)
  let I := (D.gens.zip D.invExp).map fun p => powK d (getR d R p.1) (p.2 - 1)
  dataOK2 d A B D &&
    (List.finRange m).all (fun i =>
      decide (0 < D.invExp.getD i.val 0) &&
        Nat.beq (powK d (G.getD i.val 0) (D.invExp.getD i.val 0)) (idF d) &&
        (if D.e i = 0 then Nat.beq (G.getD i.val 0) (evalWK2 d G I (commW (D.cw i).1 (D.cw i).2))
          else decide (D.e i < 65536) && Nat.beq (powK d (G.getD i.val 0) (D.e i)) (idF d))) &&
    D.rels.all fun w => Nat.beq (evalWK2 d G I w) (idF d)

@[expose] noncomputable def coverOrbitK2 {m : Nat} (d A B : Nat) (D : CoverData m)
    (ng t : Nat) (masks : List Nat) : Bool :=
  let R := runK d A B D.nregs D.prog
  dataOK2 d A B D && decide (ng ≤ m) && decide (t < d) &&
    orbitK (fun v X => vmF d X v) ((D.gens.take ng).map (getR d R)) (pw2 t) masks

end F2

section F3

open CFSG.KC.LQT CFSG.KC.OpsLayK

@[expose] noncomputable def evalWKL {m : Nat} (c : Lay) (G I : List Nat) :
    List (Fin m × Bool) → Nat
  | [] => c.ONE
  | x :: w => c.mul (if x.2 then G.getD x.1.val 0 else I.getD x.1.val 0) (evalWKL c G I w)

@[expose] def dataOKL {m : Nat} (D : CoverData m) : Bool :=
  progOK D.nregs D.prog && decide (D.gens.length = m) && decide (D.invExp.length = m) &&
    D.gens.all (fun r => decide (r < D.nregs)) && D.invExp.all (fun e => decide (e < 65536))

@[expose] noncomputable def coverKL {m : Nat} (c : Lay) (A B : Nat) (D : CoverData m) : Bool :=
  dataOKL D &&
  runC c D.prog (initR c A B D.nregs) fun R =>
    let G := D.gens.map (getR c R)
    let I := (D.gens.zip D.invExp).map fun p => powK c (getR c R p.1) (p.2 - 1)
    (List.finRange m).all (fun i =>
      decide (0 < D.invExp.getD i.val 0) &&
        Nat.beq (powK c (G.getD i.val 0) (D.invExp.getD i.val 0)) c.ONE &&
        (if D.e i = 0 then Nat.beq (G.getD i.val 0) (evalWKL c G I (commW (D.cw i).1 (D.cw i).2))
          else decide (D.e i < 65536) && Nat.beq (powK c (G.getD i.val 0) (D.e i)) c.ONE)) &&
    D.rels.all fun w => Nat.beq (evalWKL c G I w) c.ONE

@[expose] noncomputable def coverOrbitKL {m : Nat} (c : Lay) (A B : Nat) (D : CoverData m)
    (ng t : Nat) (masks : List Nat) : Bool :=
  dataOKL D && decide (ng ≤ m) && decide (t < c.d) &&
  runC c D.prog (initR c A B D.nregs) fun R =>
    orbitK (fun v X => c.vec v X) ((D.gens.take ng).map (getR c R)) (c.unit t) masks

end F3

end CFSG.KC.CoverCK

end

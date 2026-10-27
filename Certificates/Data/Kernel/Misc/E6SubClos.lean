module

public import Certificates.Data.Kernel.Misc.E6ConjOrb

public section

namespace CFSG.KC.Misc.E6Std

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def letL (l : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k List.nil)
    (fun x _ ih k => letB x fun x => ih fun ys => k (List.cons x ys)) l k

@[expose] noncomputable def conjStepThenK (G Gi : Nat → Nat) (steps : List (Nat × Nat))
    (k : List Nat → Bool) (acc : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun acc => k acc)
    (fun s _ ih acc => Prod.rec (motive := fun _ => Bool) (fun p j =>
      andB (Nat.blt p (lenN acc))
        (letB (mulB (mulB (G j) (nthV acc p)) (Gi j)) fun y =>
          andB (notB (memN y acc)) (ih (snocN acc y)))) s) steps acc

@[expose] noncomputable def conjOrbThenK (a ai b bi : Nat) (steps : List (Nat × Nat)) (z : Nat)
    (k : List Nat → Bool) : Bool :=
  letB a fun a => letB ai fun ai => letB b fun b => letB bi fun bi => letB z fun z =>
    conjStepThenK (fun j => Bool.rec (motive := fun _ => Nat) b a (Nat.beq j 0))
      (fun j => Bool.rec (motive := fun _ => Nat) bi ai (Nat.beq j 0)) steps k (List.cons z List.nil)

@[expose] noncomputable def mulStepK (G : Nat → Nat) (n : Nat) (steps : List (Nat × Nat))
    (k : List Nat → Bool) (acc : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun acc => k acc)
    (fun s _ ih acc => Prod.rec (motive := fun _ => Bool) (fun p j =>
      andB (Nat.blt j n) (andB (Nat.blt p (lenN acc))
        (letB (mulB (nthV acc p) (G j)) fun y =>
          andB (notB (memN y acc)) (ih (snocN acc y))))) s) steps acc

@[expose] noncomputable def closedK (gs L : List Nat) : Bool :=
  allL L fun x => allL gs fun g => memN (mulB x g) L

@[expose] noncomputable def subClosK (gens : List Nat) (steps : List (Nat × Nat))
    (k : List Nat → Bool) : Bool :=
  letL gens fun gs => letB oneB fun one =>
    mulStepK (fun j => nthV gs j) (lenN gs) steps (fun L => andB (closedK gs L) (k L))
      (List.cons one List.nil)

@[expose] noncomputable def invInK (Q L : List Nat) : Bool :=
  letB oneB fun one => allL Q fun q =>
    orB (notB (Nat.beq (mulB q q) one)) (orB (Nat.beq q one) (memN q L))

@[expose] noncomputable def wordsB (ls : List Nat) (ws : List (List Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun w _ ih => List.cons (Prod.rec (motive := fun _ => Nat) (fun l e => powB (lineB ls l) e) w)
      ih) ws

@[expose] noncomputable def wordsLt (n : Nat) (tw : List Nat) (ws : List (List Nat × Nat)) : Bool :=
  andB (allL tw fun i => Nat.blt i n)
    (List.rec (motive := fun _ => Bool) true
      (fun w _ ih => andB (Prod.rec (motive := fun _ => Bool) (fun l _ => allL l fun i => Nat.blt i n) w)
        ih) ws)

@[expose] noncomputable def invClassK (ls tw : List Nat) (te : Nat) (qws : List (List Nat × Nat))
    (qsteps steps : List (Nat × Nat)) (i1 i2 : Nat) : Bool :=
  andB (Nat.beq (lenN ls) 4) (andB (wordsLt 4 tw qws) <|
  letL ls fun ls => letB (powB (lineB ls tw) te) fun t => letL (wordsB ls qws) fun gs =>
    andB (Nat.beq (mulB (nthV ls 0) (nthV ls 1)) oneB)
    (andB (Nat.beq (mulB (nthV ls 2) (nthV ls 3)) oneB)
    (andB (ordB t 2) (andB (allL gs fun q => Nat.beq (mulB q t) (mulB t q))
      (subClosK gs qsteps fun Q =>
        conjOrbThenK (nthV ls 0) (nthV ls 1) (nthV ls 2) (nthV ls 3) steps t fun L =>
          andB (invInK Q L) (andB (Nat.blt i1 (lenN L)) (andB (Nat.blt i2 (lenN L))
            (ordB (mulB (mulB t (nthV L i1)) (nthV L i2)) 7))))))))

end CFSG.KC.Misc.E6Std

end

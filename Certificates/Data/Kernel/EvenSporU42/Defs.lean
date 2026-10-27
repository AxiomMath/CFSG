module

public import Certificates.Data.Kernel.SporSch.MathieuOC

public section

namespace CFSG.KC.EvenSporU42

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.MOC

@[expose] noncomputable def pgH (P i : Nat) : Nat := pg 6 (mask 6) P i

@[expose] noncomputable def mulH (P Q : Nat) : Nat := pcomp 45 6 (mask 6) P Q

@[expose] noncomputable def invH (P : Nat) : Nat := pinvS 45 6 (mask 6) P

@[expose] noncomputable def oneH : Nat := pidn 45 6

@[expose] noncomputable def eqH (P Q : Nat) : Bool :=
  (List.range 45).all fun i => Nat.beq (pgH P i) (pgH Q i)

@[expose] noncomputable def memH (P : Nat) (L : List Nat) : Bool := L.any (eqH P)

@[expose] noncomputable def commH (P Q : Nat) : Bool :=
  (List.range 45).all fun i => Nat.beq (pgH P (pgH Q i)) (pgH Q (pgH P i))

@[expose] noncomputable def wordH (X Y : Nat) : List Nat → Nat
  | [] => oneH
  | l :: w => mulH (if l = 0 then X else Y) (wordH X Y w)

@[expose] noncomputable def elemH (LR TR : Nat → Nat) (j : Nat) : Nat :=
  elemK 45 6 (mask 6) (45 * 6) (pidn 45 6) LR TR 4 j

@[expose] noncomputable def closureStepH (gens S : List Nat) : List Nat :=
  S.foldl (fun acc x => gens.foldl (fun acc' g =>
    if memH (mulH g x) acc' = true then acc' else acc' ++ [mulH g x]) acc) S

@[expose] noncomputable def closureListH (gens : List Nat) : Nat → List Nat → List Nat
  | 0, S => S
  | n + 1, S => closureListH gens n (closureStepH gens S)

@[expose] noncomputable def plH (BL PC : List Nat) : List Nat := BL.filter fun g => memH g PC

@[expose] noncomputable def plMulH (PL : List Nat) : Bool :=
  PL.all fun x => PL.all fun y => memH (mulH x y) PL

@[expose] noncomputable def plExpH (PL : List Nat) : Bool :=
  PL.all fun x => eqH (mulH x (mulH x x)) oneH

@[expose] noncomputable def blNormH (BL PL : List Nat) : Bool :=
  BL.all fun x => PL.all fun p => memH (mulH (mulH x p) (invH x)) PL

@[expose] noncomputable def cosetRepsH (PL T : List Nat) : List Nat :=
  T.foldl (fun reps x =>
    if reps.any (fun r => memH (mulH x (invH r)) PL) = true then reps else reps ++ [x]) []

@[expose] noncomputable def conjSetH (BL : List Nat) (a : Nat) : List Nat :=
  BL.filter fun x => eqH (mulH (mulH x a) (invH x)) a || eqH (mulH (mulH x a) (invH x)) (invH a)

@[expose] noncomputable def cosetCheckH (BL PL : List Nat) (a : Nat) : Bool :=
  decide ((cosetRepsH PL (conjSetH BL a)).length ≤ 6) &&
    (conjSetH BL a).all fun x => (cosetRepsH PL (conjSetH BL a)).any fun r =>
      memH (mulH x (invH r)) PL

@[expose] noncomputable def zDataH (BL PL : List Nat) (z : Nat) : Bool :=
  !eqH z oneH &&
    (PL.any fun x => PL.any fun y => eqH z (mulH (mulH (mulH x y) (invH x)) (invH y))) &&
    (PL.all fun a => eqH a oneH || eqH a z || eqH (invH a) z || cosetCheckH BL PL a)

@[expose] noncomputable def allH (BL PC : List Nat) (z : Nat) : Bool :=
  Nat.beq BL.length 648 && Nat.beq (plH BL PC).length 27 && plMulH (plH BL PC) &&
    plExpH (plH BL PC) && blNormH BL (plH BL PC) && zDataH BL (plH BL PC) z

end CFSG.KC.EvenSporU42

end

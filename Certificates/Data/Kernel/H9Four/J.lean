module

public import Certificates.Data.H9FourJ
public import Certificates.Data.Kernel.H9Four.Pk

public section

namespace CFSG.KC.H9Four.J

open CFSG.Quasithin.H13.H9Four CFSG.KC.H9Four

@[expose] noncomputable def eqE (s t : Nat) : Bool :=
  Nat.beq (fa s) (fa t) && Nat.beq (fai s) (fai t) && Nat.beq (fb s) (fb t)

@[expose] noncomputable def memE (t : Nat) (L : List Nat) : Bool := L.any fun s => eqE t s

@[expose] noncomputable def nodupE (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a l ih => !(memE a l) && ih) L

@[expose] noncomputable def codeK (p : Nat × Nat × Bool) : Nat :=
  mkE p.1 p.2.1 (Bool.rec (motive := fun _ => Nat) 0 1 p.2.2)

@[expose] noncomputable def conjK (s x : Nat) : Nat := mulE (mulE s x) (invE s)

@[expose] noncomputable def closedK (E Γ : List Nat) : Bool :=
  E.all fun e => Γ.all fun g => memE (mulE e g) E && memE (mulE e (invE g)) E

@[expose] noncomputable def pow3K (y : Nat) : List Nat := [oneE, y, mulE y y]

@[expose] noncomputable def anyFixK (G : List Nat) (y : Nat) : Bool :=
  (List.range 256).any fun w => (fixAllK G).testBit w && !(actK y w == w)

@[expose] noncomputable def u0K : List Nat := gensK u0Codes
@[expose] noncomputable def s0K : Nat := codeK s0Code
@[expose] noncomputable def s0GensK : List Nat := u0K ++ [s0K]
@[expose] noncomputable def s0ListK : List Nat :=
  elemsK u0K ++ (elemsK u0K).map fun u => mulE u s0K
@[expose] noncomputable def j0GensK : List Nat := gensK j0Codes
@[expose] noncomputable def j0ListK : List Nat := elemsK j0GensK
@[expose] noncomputable def y1K : Nat := codeK y1Code
@[expose] noncomputable def y2K : Nat := codeK y2Code
@[expose] noncomputable def x0GensK : List Nat := j0GensK ++ [y1K, y2K]
@[expose] noncomputable def x0ListK : List Nat :=
  j0ListK.flatMap fun j => (pow3K y1K).flatMap fun a => (pow3K y2K).map fun b => mulE (mulE j a) b
@[expose] noncomputable def e9GensK : List Nat := [y1K, y2K]
@[expose] noncomputable def e9ListK : List Nat :=
  (pow3K y1K).flatMap fun a => (pow3K y2K).map fun b => mulE a b
@[expose] noncomputable def linesK : List (Nat × Nat) := lineCodes.map fun p => (codeK p.1, codeK p.2)
@[expose] noncomputable def lineListK (y : Nat) : List Nat :=
  j0ListK ++ j0ListK.map (fun j => mulE j y) ++ j0ListK.map (fun j => mulE j (mulE y y))
@[expose] noncomputable def lineListsK : List (List Nat) := linesK.map fun p => lineListK p.1

@[expose] noncomputable def s0CheckK : Bool :=
  s0GensK.all validE && closedK s0ListK s0GensK && nodupE s0ListK && s0ListK.length == 128

@[expose] noncomputable def j0CheckK : Bool :=
  j0GensK.all (fun g => validE g && eqE (mulE g g) oneE && !eqE g oneE && !Nat.beq (fb g) 1) &&
    j0GensK.all (fun g => j0GensK.all fun h => eqE (mulE g h) (mulE h g)) && nodupE j0ListK &&
    j0GensK.all (fun g => memE g s0ListK)

@[expose] noncomputable def x0CheckK : Bool :=
  x0GensK.all (fun x => validE x && !Nat.beq (fb x) 1) && memE oneE x0ListK &&
    closedK x0ListK x0GensK && nodupE x0ListK && x0ListK.length == 144 &&
    x0GensK.all (fun x => j0GensK.all fun j => memE (conjK x j) j0ListK) &&
    s0GensK.all (fun s => x0GensK.all fun x => memE (conjK s x) x0ListK) &&
    x0ListK.all (fun x => memE (mulE x (mulE x x)) j0ListK) &&
    x0GensK.all (fun x => x0ListK.all fun y => memE (mulE (conjK x y) (invE y)) j0ListK)

@[expose] noncomputable def oddGenCheckK : Bool :=
  x0ListK.all fun x => x0ListK.any fun a =>
    eqE (mulE a (mulE a a)) oneE &&
      eqE (mulE (mulE (invE a) x) (mulE (mulE (invE a) x) (mulE (invE a) x))) oneE

@[expose] noncomputable def lineCheckK : Bool :=
  linesK.all (fun p => memE p.1 x0ListK && memE p.2 s0ListK &&
      eqE (mulE p.1 (mulE p.1 p.1)) oneE && nodupE (lineListK p.1) &&
      !memE (conjK p.2 p.1) (lineListK p.1)) &&
    x0ListK.all fun x => memE x j0ListK || lineListsK.any fun l => memE x l

@[expose] noncomputable def fixCheckK : Bool := pop256 (fixAllK x0GensK) == 1

@[expose] noncomputable def kerCheckK : Bool :=
  s0ListK.all fun t => memE t j0ListK ||
    x0GensK.any fun x => !memE (mulE (conjK t x) (invE x)) j0ListK

@[expose] noncomputable def e9CheckK : Bool :=
  memE oneE e9ListK && closedK e9ListK e9GensK && nodupE e9ListK && e9ListK.length == 9 &&
    pop256 (fixAllK e9GensK) == 1 && anyFixK j0GensK y1K

@[expose] noncomputable def ffRepCheckK : Bool :=
  repCodes.all fun gs => canonK gs && ((gensK gs).isEmpty ||
    decide (2 ^ (gensK gs).length * pop256 (fixAllK (gensK gs)) < 256) || (gensK gs).length == 4)

@[expose] noncomputable def u0CheckK : Bool :=
  s0ListK.all fun e => Nat.beq (fb e) 1 || !eqE (mulE e e) oneE || eqE e oneE || memE e j0ListK ||
    decide ((s0ListK.filter fun g =>
      !Nat.beq (fb g) 1 && eqE (mulE g g) oneE && eqE (mulE g e) (mulE e g)).length ≤ 12)

@[expose] noncomputable def canonDataK : Bool :=
  canonK u0Codes && canonK [s0Code] && canonK j0Codes && canonK [y1Code] && canonK [y2Code] &&
    lineCodes.all fun p => canonK [p.1] && canonK [p.2]

end CFSG.KC.H9Four.J

end

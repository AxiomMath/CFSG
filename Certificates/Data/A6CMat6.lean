module

public import Certificates.Data.A6CMat

public section

namespace Certificates.A6C

@[expose] def sM6 (_ : Unit := ()) : Mat :=
  Array.ofFn (n := 36) fun p =>
    let i := p.val / 6
    let j := p.val % 6
    if i / 2 == j / 2 then (if i % 2 == 0 then 1 else (if j % 2 == 0 then 2 else 1)) else 0

@[expose] def gens6 (_ : Unit := ()) : Array Mat :=
  #[reflM 6 #[1,0,0,0,0,0], reflM 6 #[1,1,0,0,0,0], reflM 6 #[1,0,1,1,1,0],
    reflM 6 #[1,1,1,1,0,0], reflM 6 #[1,1,1,1,1,0], reflM 6 #[0,1,1,0,0,0],
    reflM 6 #[1,1,1,0,0,1], sM6 ()]

@[expose] def a0M6 (_ : Unit := ()) : Mat :=
  #[2,0,0,0,0,0, 0,2,0,0,0,0, 0,0,1,0,0,0, 0,0,0,1,0,0, 0,0,0,0,1,0, 0,0,0,0,0,1]

@[expose] def g0M6 (_ : Unit := ()) : Mat :=
  #[0,1,1,1,0,2, 0,2,2,2,1,0, 2,2,0,0,2,2, 2,0,2,0,2,2, 2,0,0,2,2,2, 1,2,2,2,0,0]

@[expose] def nM6 (_ : Unit := ()) : Mat :=
  #[0,2,1,2,1,0, 2,1,1,0,0,1, 1,1,1,0,0,2, 2,0,0,1,1,2, 1,0,0,1,1,1, 0,2,1,1,2,0]

@[expose] def eaM6 (_ : Unit := ()) : Array Mat :=
  #[
    #[2,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1],
    #[0,2,0,0,0,0,2,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1],
    #[1,1,0,0,0,0,2,1,0,0,0,0,0,0,1,1,0,0,0,0,2,1,0,0,0,0,0,0,1,1,0,0,0,0,2,1],
    #[1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,2,0,0,0,0,2,0,0,0,0,0,0,0,1,0,0,0,0,0,0,1],
    #[1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,0,0,0,2,0,0,0,0,0,0,1],
    #[1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,2,0,0,0,1,0,0,0,0,0,0,1,0,0,0,2,0,0,0]
  ]

@[expose] def etM6 (_ : Unit := ()) : Array Mat :=
  #[
    #[2,0,1,1,1,0,0,1,0,0,0,0,1,0,2,1,1,0,1,0,1,2,1,0,1,0,1,1,2,0,0,0,0,0,0,1],
    #[2,2,2,2,0,0,2,2,1,1,0,0,2,1,2,1,0,0,2,1,1,2,0,0,0,0,0,0,1,0,0,0,0,0,0,1],
    #[2,0,1,1,1,0,0,2,1,1,1,0,1,1,0,2,2,0,1,1,2,0,2,0,1,1,2,2,0,0,0,0,0,0,0,1],
    #[2,1,2,0,0,2,1,2,2,0,0,2,2,2,2,0,0,1,0,0,0,1,0,0,0,0,0,0,1,0,2,2,1,0,0,2],
    #[2,0,0,0,0,0,0,0,2,2,1,2,0,2,0,1,2,1,0,2,1,0,2,1,0,1,2,2,0,2,0,2,1,1,2,0],
    #[2,2,0,1,2,1,1,2,0,1,2,1,0,1,2,2,2,1,0,1,0,1,0,0,0,0,0,0,1,1,0,2,2,1,1,2]
  ]

@[expose] def tauM (n : Nat) (g : Mat) : Mat :=
  negM (addM (addM g (powM n g 2)) (addM (powM n g 3) (powM n g 4)))

@[expose] def part61 (rA rCA : Rec) : Bool :=
  classOK 6 (gens6 ()) (a0M6 ()) rA 2835 && centOK 6 (eaM6 ()) (a0M6 ()) rCA 9216

@[expose] def part62 (rT rCT : Rec) : Bool :=
  let g0 := g0M6 ()
  let tau := tauM 6 g0
  simOK 6 g0 && !(eqP g0 (idN 6)) && powM 6 g0 5 == idN 6 &&
    simOK 6 tau && eqP (mulN 6 tau tau) (idN 6) &&
    classOK 6 (gens6 ()) tau rT 4536 && centOK 6 (etM6 ()) tau rCT 5760 &&
    (k0Of 6 g0 rCT).length == 40

@[expose] def part63 (_ : Unit := ()) : Bool :=
  let g0 := g0M6 ()
  simOK 6 (nM6 ()) && eqP (mulN 6 (nM6 ()) g0) (mulN 6 (mulN 6 g0 g0) (nM6 ()))

@[expose] def part64 (rA rCT : Rec) : Bool :=
  let g0 := g0M6 ()
  let K0 := k0Of 6 g0 rCT
  let I := idN 6
  rA.L.toList.all fun a =>
    !(relP 6 a g0) ||
      (let K := K0.filter fun c => commP 6 c a
       decide (K.length ≤ 4) && K.all fun c => eqP (mulN 6 c c) I)

end Certificates.A6C

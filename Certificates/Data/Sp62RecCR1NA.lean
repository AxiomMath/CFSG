module

public import Certificates.Data.Sp62RecCR1

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73.Yamaki Matrix

@[expose] def centA0Check (_ : Unit := ()) : Bool :=
  let L := (enumH ()).elems
  let EA := enumA0 ()
  let gs := gA0 ()
  allLt L.size fun i => !(commOK gs L[i]!) || (EA.lookup L[i]!).isSome

@[expose] def normA0Check (_ : Unit := ()) : Bool :=
  let G := genA ()
  let EA := enumA0 ()
  let gs := gA0 ()
  idxN0.all fun s => allLt gs.size fun j =>
    (EA.lookup (compA (compA G[s]! gs[j]!) G[s]!)).isSome

@[expose] def wCodes : List ℕ := [0, 9, 20, 29, 38, 47, 50, 59]

@[expose] def wCheck (_ : Unit := ()) : Bool :=
  let L := (enumA0 ()).elems
  let gs := gA0 ()
  (allLt L.size fun i => wCodes.all fun w => decide ((L[i]!)[w]! = w)) &&
    allLt 64 fun v => !(allLt gs.size fun j => decide ((gs[j]!)[v]! = v)) || wCodes.contains v

@[expose] def stabWCheck (_ : Unit := ()) : Bool :=
  let L := (enumH ()).elems
  let EX := enumX ()
  allLt L.size fun i =>
    !(wCodes.all fun w => wCodes.contains (L[i]!)[w]!) || (EX.lookup L[i]!).isSome

@[expose] def centAlphaCheck (_ : Unit := ()) : Bool :=
  let L := (enumN ()).elems
  let EX := enumX ()
  let a := (genA ())[5]!
  allLt L.size fun i => !(decide (compA L[i]! a = compA a L[i]!)) || (EX.lookup L[i]!).isSome

@[expose] def sylMeetWord : List ℕ := [9, 10, 9]

@[expose] def sylMeetCheck (_ : Unit := ()) : Bool :=
  let ES := enumS0 ()
  let L := ES.elems
  let EA := enumA0 ()
  let G := genA ()
  let g := wordA G sylMeetWord
  let gi := wordA G sylMeetWord.reverse
  wordsIn idxN0 [sylMeetWord] && allLt L.size fun i =>
    !(ES.lookup (compA (compA gi L[i]!) g)).isSome || (EA.lookup L[i]!).isSome

@[expose] def orbAlphaWords : List (List ℕ) :=
  [[], [9], [0, 9], [10, 9], [2, 10, 9], [10, 0, 9], [2, 10, 0, 9]]

@[expose] def orbPi12Words : List (List ℕ) :=
  [[], [10], [2, 10], [9, 10], [0, 9, 10], [9, 2, 10], [0, 9, 2, 10]]

@[expose] def orbPi3Words : List (List ℕ) :=
  [[], [9], [10], [0, 9], [2, 10], [9, 10], [10, 9], [0, 9, 10], [2, 10, 9], [9, 2, 10],
    [9, 10, 9], [10, 0, 9], [0, 9, 2, 10], [0, 9, 10, 9], [2, 10, 0, 9], [9, 2, 10, 9],
    [9, 10, 0, 9], [0, 9, 2, 10, 9], [0, 9, 10, 0, 9], [2, 0, 9, 10, 9], [9, 2, 10, 0, 9]]

@[expose] def orbRhoWords : List (List ℕ) :=
  [[], [0], [2], [9], [10], [0, 9], [2, 0], [2, 10], [9, 0], [9, 2], [10, 0], [10, 2],
    [0, 9, 0], [0, 9, 2], [2, 10, 0], [2, 10, 2], [9, 2, 0], [9, 10, 2], [10, 2, 0], [10, 9, 0],
    [0, 9, 2, 0], [0, 9, 10, 2], [2, 10, 2, 0], [2, 10, 9, 0], [9, 10, 2, 0], [10, 9, 2, 0],
    [2, 10, 9, 2, 0], [9, 10, 9, 2, 0]]

@[expose] def orbCodes (x : List ℕ) (cs : List (List ℕ)) : List (Array ℕ) :=
  let G := genA ()
  cs.map fun c => wordA G (conjWord c x)

@[expose] def closedN0 (G : Array (Array ℕ)) (l : List (Array ℕ)) : Bool :=
  idxN0.all fun s => l.all fun y => l.contains (compA (compA G[s]! y) G[s]!)

@[expose] def orbCheck (_ : Unit := ()) : Bool :=
  let G := genA ()
  let one := idA ()
  let la := orbCodes [5] orbAlphaWords
  let lb := orbCodes [4] orbPi12Words
  let lc := orbCodes [5, 4] orbPi3Words
  let ld := orbCodes [3, 7] orbRhoWords
  let all := la ++ lb ++ lc ++ ld
  let L := (enumA0 ()).elems
  wordsIn idxN0 (orbAlphaWords ++ orbPi12Words ++ orbPi3Words ++ orbRhoWords) &&
    decide all.Nodup && closedN0 G la && closedN0 G lb && closedN0 G lc && closedN0 G ld &&
    allLt L.size fun i => decide (L[i]! = one) || all.contains L[i]!

@[expose] def e8Check (_ : Unit := ()) : Bool :=
  let one := idA ()
  let lb := orbCodes [4] orbPi12Words
  !(lb.contains one) &&
    lb.all fun y => lb.all fun z => decide (compA y z = one) || lb.contains (compA y z)

@[expose] def sevenWord : List ℕ := [0, 9, 10]

@[expose] def sevenCheck (_ : Unit := ()) : Bool :=
  let G := genA ()
  let one := idA ()
  let x := wordA G sevenWord
  let L := (enumA0 ()).elems
  wordsIn idxN0 [sevenWord] && decide (wordA G (List.replicate 7 sevenWord).flatten = one) &&
    !(decide (x = one)) && allLt L.size fun i =>
      !(decide (compA L[i]! x = compA x L[i]!)) || decide (L[i]! = one)

@[expose] def rhoP6 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 1, 0, 0; 0, 0, 1, 0, 1, 0; 0, 1, 1, 0, 0, 1; 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0]

@[expose] def rhoPinv6 : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1; 1, 0, 0, 1, 0, 0; 0, 1, 0, 0, 0, 1;
    0, 0, 1, 0, 1, 1]

@[expose] def rhoP : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  rhoP6.submatrix finSumFinEquiv finSumFinEquiv

@[expose] def rhoPinv : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  rhoPinv6.submatrix finSumFinEquiv finSumFinEquiv

@[expose] def rhoMatCheck (_ : Unit := ()) : Bool :=
  decide (rhoP * rhoPinv = 1) && decide (rhoPinv * rhoP = 1) &&
    decide (∀ j : Fin 3, rhoP *ᵥ Pi.single (Sum.inl j) 1 = vecOf (![9, 20, 38] j)) &&
    (List.finRange 12).all fun i =>
      !(idxN0.contains i.val) || decide ((rhoPinv * yamakiMat i * rhoP).toBlocks₂₁ = 0)

@[expose] def rhoKerCheck (_ : Unit := ()) : Bool :=
  let L := (enumN ()).elems
  let EA := enumA0 ()
  allLt L.size fun i =>
    !([9, 20, 38].all fun w => decide ((L[i]!)[w]! = w)) || (EA.lookup L[i]!).isSome

@[expose] def alphaClassWords : List (List ℕ) :=
  [[], [9], [0, 9], [10, 9], [2, 10, 9], [10, 0, 9], [11, 10, 9], [2, 10, 0, 9], [8, 11, 10, 9],
    [10, 11, 10, 9], [11, 2, 10, 9], [11, 10, 0, 9], [2, 10, 11, 10, 9], [8, 11, 2, 10, 9],
    [8, 11, 10, 0, 9], [9, 10, 11, 10, 9], [10, 8, 11, 10, 9], [10, 11, 2, 10, 9],
    [10, 11, 10, 0, 9], [11, 2, 10, 0, 9], [0, 9, 10, 11, 10, 9], [2, 10, 8, 11, 10, 9],
    [2, 10, 11, 2, 10, 9], [2, 10, 11, 10, 0, 9], [8, 2, 10, 11, 10, 9], [8, 11, 2, 10, 0, 9],
    [9, 2, 10, 11, 10, 9], [9, 10, 8, 11, 10, 9], [9, 10, 11, 2, 10, 9], [9, 10, 11, 10, 0, 9],
    [10, 8, 11, 2, 10, 9], [10, 8, 11, 10, 0, 9], [10, 11, 2, 10, 0, 9],
    [0, 9, 2, 10, 11, 10, 9], [0, 9, 10, 8, 11, 10, 9], [0, 9, 10, 11, 2, 10, 9],
    [0, 9, 10, 11, 10, 0, 9], [2, 10, 8, 11, 10, 0, 9], [2, 10, 11, 2, 10, 0, 9],
    [7, 0, 9, 10, 11, 10, 9], [8, 2, 10, 11, 10, 0, 9], [9, 2, 10, 8, 11, 10, 9],
    [9, 2, 10, 11, 2, 10, 9], [9, 2, 10, 11, 10, 0, 9], [9, 8, 2, 10, 11, 10, 9],
    [9, 10, 8, 11, 2, 10, 9], [9, 10, 8, 11, 10, 0, 9], [9, 10, 11, 2, 10, 0, 9],
    [10, 8, 11, 2, 10, 0, 9], [0, 9, 2, 10, 8, 11, 10, 9], [0, 9, 2, 10, 11, 2, 10, 9],
    [0, 9, 2, 10, 11, 10, 0, 9], [0, 9, 8, 2, 10, 11, 10, 9], [0, 9, 10, 8, 11, 2, 10, 9],
    [0, 9, 10, 11, 2, 10, 0, 9], [2, 0, 9, 10, 11, 2, 10, 9], [7, 0, 9, 2, 10, 11, 10, 9],
    [7, 0, 9, 10, 11, 2, 10, 9], [9, 2, 10, 8, 11, 10, 0, 9], [9, 2, 10, 11, 2, 10, 0, 9],
    [9, 8, 2, 10, 11, 10, 0, 9], [9, 10, 8, 11, 2, 10, 0, 9], [0, 9, 8, 2, 10, 11, 10, 0, 9]]

@[expose] def alphaClassCheck (_ : Unit := ()) : Bool :=
  decide (alphaClassWords.length = 63) &&
    wordsIn (List.range 12) alphaClassWords &&
    decide (orbCodes [5] alphaClassWords).Nodup

end CFSG.ClassicalInvolution.Sp62Rec

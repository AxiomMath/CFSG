module

public import Certificates.Data.YamakiEnum

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def idxX0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10]

@[expose] def idxN0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

@[expose] def idxHhat : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11]

@[expose] def gWords : List (List ℕ) :=
  [[2, 0, 5, 8], [1, 10, 2, 8]]

@[expose] def nWords : List (List ℕ) :=
  [[1, 2, 6, 10, 9], [6, 0, 8, 9, 10, 2, 0]]

@[expose] def hWords : List (List ℕ) :=
  [[2, 3, 11, 8, 2, 10, 11, 8], [1, 3, 2, 6, 8, 11, 10]]

@[expose] def wordsA (gs : Array (Array ℕ)) (ws : List (List ℕ)) : Array (Array ℕ) :=
  (ws.map (wordA gs)).toArray

@[expose] def gX (_ : Unit := ()) : Array (Array ℕ) := wordsA (genA ()) gWords

@[expose] def gN (_ : Unit := ()) : Array (Array ℕ) := wordsA (genA ()) nWords

@[expose] def gH (_ : Unit := ()) : Array (Array ℕ) := wordsA (genA ()) hWords

@[expose] def enumX (_ : Unit := ()) : Enum := bfsEnum (gX ()) 1536

@[expose] def enumN (_ : Unit := ()) : Enum := bfsEnum (gN ()) 10752

@[expose] def enumH (_ : Unit := ()) : Enum := bfsEnum (gH ()) 23040

@[expose] def enumCheck (_ : Unit := ()) : Bool :=
  enumOK (enumX ()) (gX ()) && enumOK (enumN ()) (gN ()) && enumOK (enumH ()) (gH ())

@[expose] def sizeCheck (_ : Unit := ()) : Bool :=
  decide ((enumX ()).elems.size = 1536) && decide ((enumN ()).elems.size = 10752) &&
    decide ((enumH ()).elems.size = 23040)

@[expose] def wordsIn (I : List ℕ) (ws : List (List ℕ)) : Bool :=
  ws.all fun w => w.all fun i => I.contains i

@[expose] def tablesGenCheck (_ : Unit := ()) : Bool :=
  let G := genA ()
  let EX := enumX ()
  let EN := enumN ()
  let EH := enumH ()
  wordsIn idxX0 gWords && wordsIn idxN0 nWords && wordsIn idxHhat hWords &&
    idxX0.all (fun i => (EX.lookup G[i]!).isSome) &&
    idxN0.all (fun i => (EN.lookup G[i]!).isSome) &&
    idxHhat.all (fun i => (EH.lookup G[i]!).isSome)

end CFSG.ClassicalInvolution.Solomon73.Yamaki

module

public import Certificates.Data.CFSGNative.AS91.M24Kzero

public section

set_option compiler.extract_closed false

namespace CFSG.Quasithin.H13.AS91.M24G.Native

@[expose] def fusePiATab : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 9, 8, 11, 10, 13, 12, 15, 14, 17, 16, 19, 18, 21, 20, 23, 22]

@[expose] def fusePiBTab : Array Nat :=
  #[1, 0, 3, 2, 5, 4, 7, 6, 10, 11, 8, 9, 14, 15, 12, 13, 19, 18, 17, 16, 23, 22, 21, 20]

@[expose] def fuseX0Word : List Nat := [0, 0, 5, 5]

@[expose] def fuseSigmaWords : List (List Nat) := [[], [5, 6], [5, 6, 11]]

@[expose] def fuseDuadMask (_ : Unit := ()) : Nat := actM ccEColsN ((1 <<< 0) ||| (1 <<< 1))

@[expose] def fuseULetters (_ : Unit := ()) : List (Array Nat) := (kzeroHs ()).map Prod.fst

@[expose] def fuseLetters (_ : Unit := ()) : List (Array Nat) := genTabs ++ lTabs ++ uTabs ++ s0Tabs

@[expose] def fuseWord (ls : List (Array Nat)) (w : List Nat) : Array Nat :=
  w.foldl (fun t j => kzeroMul t (ls.getD j kzeroId)) kzeroId

@[expose] def fuseXorClose (gs : List Nat) : List Nat :=
  gs.foldl (fun L g => if L.contains g then L else L ++ L.map (· ^^^ g)) [0]

@[expose] def fuseCommGens (_ : Unit := ()) : List Nat :=
  (kzeroK0List ()).flatMap fun t => (List.range 11).map fun i => toddAct t (1 <<< i) ^^^ (1 <<< i)

@[noinline, expose] def fuseCommLoop (os L : List Nat) : Bool :=
  (List.range 2048).all fun m => !(toddOctsKer os m) || L.contains m

@[expose] def fuseCommCheck (_ : Unit := ()) : Bool :=
  fuseCommLoop (octsS baseSext) (fuseXorClose (fuseCommGens ()))

@[expose] def fuseDuadCheck (_ : Unit := ()) : Bool :=
  toddOctsKer (octsS baseSext) (fuseDuadMask ())

@[expose] def fusePiCheck (_ : Unit := ()) : Bool :=
  let K := kzeroK0List ()
  K.contains fusePiATab && K.contains fusePiBTab

@[expose] def fusePairs (_ : Unit := ()) : List (Array Nat × Array Nat) :=
  [(pATab, pATab), (pBTab, pBiTab), (pBiTab, pBTab)]

@[expose] def fuseConjSteps (ps : List (Array Nat × Array Nat)) : List (Array Nat → Array Nat) :=
  ps.map fun p t => kzeroConj p t

@[expose] def fuseOrbit (x : Array Nat) : Array (Array Nat) × Array Nat × Array Nat :=
  bfs kzeroKey (fuseConjSteps (fusePairs ())) x 32000

@[noinline, expose] def fuseInvLoop (S : Array (Array Nat)) (LA LB : List (Array Nat)) : Bool :=
  S.toList.all fun t => kzeroMul t t != kzeroId || t == kzeroId || LA.contains t || LB.contains t

@[expose] def fuseInvCheck (_ : Unit := ()) : Bool :=
  let steps := fuseConjSteps (fusePairs ())
  let rA := fuseOrbit fusePiATab
  let rB := fuseOrbit fusePiBTab
  treeValid kzeroValid steps fusePiATab rA && treeValid kzeroValid steps fusePiBTab rB &&
    fuseInvLoop (kzeroSyl ()).1 rA.1.toList rB.1.toList

@[expose] def fuseX0Tab (_ : Unit := ()) : Array Nat := fuseWord (fuseULetters ()) fuseX0Word

@[noinline, expose] def fuseX0Loop (T : Array Nat) (os : List Nat) (K : List (Array Nat)) : Bool :=
  K.all (fun t => t == kzeroId || kzeroMul T t != kzeroMul t T) &&
    (List.range 2048).all fun m => toddOctsKer os (toddAct T m ^^^ m)

@[expose] def fuseX0Check (_ : Unit := ()) : Bool :=
  fuseX0Loop (fuseX0Tab ()) (octsS baseSext) (kzeroK0List ())

@[noinline, expose] def fusePiBLoop (os : List Nat) : Bool :=
  (List.range 2048).all fun m => toddAct fusePiBTab m != m || toddOctsKer os m

@[expose] def fusePiBCheck (_ : Unit := ()) : Bool := fusePiBLoop (octsS baseSext)

@[noinline, expose] def fusePiALoop (os : List Nat) (Ts : List (Array Nat)) : Bool :=
  Ts.all (fun T => kzeroMul T fusePiATab == kzeroMul fusePiATab T) &&
    (List.range 2048).all fun m =>
      toddAct fusePiATab m != m || Ts.any fun T => toddOctsKer os (toddAct T m)

@[expose] def fusePiACheck (_ : Unit := ()) : Bool :=
  fusePiALoop (octsS baseSext) (fuseSigmaWords.map (fuseWord (fuseLetters ())))

@[expose] def fuseCheck (_ : Unit := ()) : Bool :=
  fuseCommCheck () && fuseDuadCheck () && fusePiCheck () && fuseInvCheck () && fuseX0Check () &&
    fusePiBCheck () && fusePiACheck ()

end CFSG.Quasithin.H13.AS91.M24G.Native

module

public import Certificates.Data.Kernel.M24G.Duad
public import Certificates.Data.CFSGNative.AS91.M24Fuse

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

@[expose] def actT (t : Array Nat) : Nat → Nat := toddActF (imgTab t.toList)

@[expose] def fuseWordF (ls : List (Array Nat)) (w : List Nat) : Array Nat :=
  w.foldl (fun t j => mulTabF t (ls.getD j Native.kzeroId)) Native.kzeroId

@[expose] def fuseCommGensK (K : List (Array Nat)) : List Nat :=
  K.flatMap fun t => (List.range 11).map fun i => Native.toddAct t (1 <<< i) ^^^ (1 <<< i)

@[expose] def xorStepM (s : List Nat × Nat) (g : Nat) : List Nat × Nat :=
  if s.2.testBit g then s else
    let L' := s.1.map (· ^^^ g)
    (s.1 ++ L', s.2 ||| orMask L')

@[expose] def xorCloseM (gs : List Nat) : List Nat × Nat := gs.foldl xorStepM ([0], orMask [0])

@[expose] def fuseCommLoopF (bad M : Nat) : Bool :=
  (List.range 2048).all fun m => bad.testBit m || M.testBit m

@[expose] def fuseX0LoopF (T : Array Nat) (bad : Nat) (K : List (Array Nat)) : Bool :=
  K.all (fun t => t == Native.kzeroId || mulTabF T t != mulTabF t T) &&
    (List.range 2048).all fun m => !bad.testBit (actT T m ^^^ m)

@[expose] def fusePiBLoopF (bad : Nat) : Bool :=
  (List.range 2048).all fun m => actT Native.fusePiBTab m != m || !bad.testBit m

@[expose] def fusePiALoopF (bad : Nat) (Ts : List (Array Nat)) : Bool :=
  Ts.all (fun T => mulTabF T Native.fusePiATab == mulTabF Native.fusePiATab T) &&
    (List.range 2048).all fun m =>
      actT Native.fusePiATab m != m || Ts.any fun T => !bad.testBit (actT T m)

@[expose] def fuseToddF (bad : Nat) (K : List (Array Nat)) : Bool :=
  fuseCommLoopF bad (xorCloseM (fuseCommGensK K)).2 &&
    fuseX0LoopF (fuseWordF (Native.fuseULetters ()) Native.fuseX0Word) bad K &&
    fusePiBLoopF bad && fusePiALoopF bad (Native.fuseSigmaWords.map (fuseWordF (Native.fuseLetters ())))

end CFSG.KC.M24G

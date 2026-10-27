module

public import CFSG.Sporadic.SuzRecog.LocalRFusionGenTests
public meta import CFSG.Sporadic.SuzRecog.LocalRFusionGenTests

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SporSuz

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.LocalR

@[expose] def evalW (gs gis : Nat → Tab) (w : List Int) : Tab :=
  w.foldr (fun (z : Int) (t : Tab) =>
    comp 1782 (if 0 < z then gs (z.natAbs - 1) else gis (z.natAbs - 1)) t) (idTab 1782)

@[expose] def gWord : List Int :=
  [-2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1,
    -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, 1, 2, 1, -2, 1, -2, 1,
    2, 1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1,
    -2, -1, 2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2,
    -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2,
    1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2,
    1, 2, 1, 2, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1,
    -2, -1, 2, -1, -2, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2,
    1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, -1, 2, -1, -2,
    -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2,
    1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, -1, -2, -1, -2, -1, -2,
    -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2]

@[expose] def b0Word : List Int :=
  [-1, 2, 3, 2, -3, -1, -1, -3, -1, 2, 2, -1, -3, -1, 2, 2, -1, -3, -1, 2,
    2, -1, 3, 1, -2, -2, 3, 1, -2, 1, 3, 1, -2, -1, -2, -1, -2, 3, -2, -1,
    -3, -1, 2, 2, 1, 2, -3, 1, 2, 2, 1, 2, -3, -1, 2, -1, -2, -2, -2, -2,
    -2, 3]

@[expose] def b1Word : List Int :=
  [-1, -2, -1, -2, -2, 1, -2, 1, -2, -2, 1, -2, 1, -2, 1, -2]

@[expose] def s1PosT : Nat := 174

@[expose] def s1PosV : Nat := 8113

@[expose] def s1PosW : Nat := 8149

@[expose] def abG (j : Nat) : Tab := if j = 0 then b0Arr else b1Arr

@[expose] def abI (j : Nat) : Tab := invTab 1782 (abG j)

@[expose] def gTab (_ : Unit := ()) : Tab := evalW abG abI gWord

@[expose] def cgG (j : Nat) : Tab := if j = 0 then cTab 2 else if j = 1 then cTab 4 else gTab ()

@[expose] def cgI (j : Nat) : Tab := invTab 1782 (cgG j)

@[expose] def commT (x y : Tab) : Bool := comp 1782 x y == comp 1782 y x

@[expose] def commZT (x y : Tab) : Bool := comp 1782 x y == comp 1782 tTab (comp 1782 y x)

@[expose] def sizesOK (_ : Unit := ()) : Bool :=
  tTab.size == 1782 && b0Arr.size == 1782 && b1Arr.size == 1782 && (cTab 2).size == 1782 &&
    (cTab 4).size == 1782

@[expose] def lettersOK (_ : Unit := ()) : Bool :=
  gWord.all (fun z => decide (z.natAbs - 1 < 2)) &&
    b0Word.all (fun z => decide (z.natAbs - 1 < 3)) &&
    b1Word.all (fun z => decide (z.natAbs - 1 < 3))

@[expose] def inverseTabsOK (_ : Unit := ()) : Bool :=
  (List.range 2).all (fun j => (abI j).size == 1782 && comp 1782 (abI j) (abG j) == idTab 1782) &&
    (List.range 3).all (fun j => (cgI j).size == 1782 && comp 1782 (cgI j) (cgG j) == idTab 1782)

@[expose] def s1EnumOK (_ : Unit := ()) : Bool :=
  s1Enum.tabs.size == 8192 && s1Enum.tabs[0]! == idTab 1782 && s1Enum.tabs[s1PosT]! == tTab

@[expose] def centerOK (_ : Unit := ()) : Bool :=
  (List.range 8192).filter (fun i => s1Gens.all fun y => commT s1Enum.tabs[i]! y) == [0, s1PosT]

@[expose] def z2OK (_ : Unit := ()) : Bool :=
  (List.range 8192).filter (fun i => s1Gens.all fun y =>
    commT s1Enum.tabs[i]! y || commZT s1Enum.tabs[i]! y) == [0, s1PosT, s1PosV, s1PosW]

@[expose] def conjInV (g x : Tab) : Bool :=
  [s1PosT, s1PosV, s1PosW].any fun u => comp 1782 g x == comp 1782 s1Enum.tabs[u]! g

@[expose] def gNormOK (_ : Unit := ()) : Bool :=
  conjInV (gTab ()) tTab && conjInV (gTab ()) s1Enum.tabs[s1PosV]! && !commT (gTab ()) tTab

@[expose] def genOK (_ : Unit := ()) : Bool :=
  evalW cgG cgI b0Word == b0Arr && evalW cgG cgI b1Word == b1Arr

@[expose] def suzPairOK (_ : Unit := ()) : Bool :=
  sizesOK () && lettersOK () && inverseTabsOK () && s1EnumOK () && centerOK () && z2OK () &&
    gNormOK () && genOK ()

end CFSG.LocalAnalysis.WeakClosure81.SporSuz

end

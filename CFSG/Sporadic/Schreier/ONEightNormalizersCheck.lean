module

public import CFSG.Sporadic.Schreier.ONCheckLocalInputs
public meta import CFSG.Sporadic.Schreier.ONCheckLocalInputs

public section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

@[expose] def onE8Words : Array (Array (List Int)) :=
  #[#[[4, 4], [-3, 2], [2, 2]], #[[4, 4], [2, 2], [4, 1]]]

@[expose] def onNormWords : Array (List Int) := #[
    [3, 6, 2, 4, 2, 3, 2, 3, 3, 6, 4, 4, 4, 3, 4, 4, -5, -4, 7, 6],
    [-7, 6, -7, -6, 3, 3, -4, -3, -3, -3, -4, -4, -4, -3, -3, -3, 1, -3, -7, -5, -6, -5, -2],
    [7, -6, 7, -6, -3, -3, -3, -3, -3, -3, -3, -4, -4, -4, -4, -3, -3, -4, -3, -2, -2, -1, -5,
      -2, -7, -7],
    [6, -7, 6, 4, -3, -3, -4, -4, -3, -4, -4, -3, -6, -3, -2, -2, -1, -4, -1, -4, -5]]

@[expose] def onNormTags : Array Nat := #[0, 0, 1, 1]

@[expose] def onAWord : List Int :=
  [-3, -3, -3, -3, -4, -4, 3, -4, -4, -3, -2, -3, 1, 3, 4, -1, 4, -3, -2, -4, -4, -1, 4, -3, -2,
    -4, -4, -4, -4, -1, 4, -3, -2, 3, -4, -1, 4, -3, -2, -1, 4, -3, -2, -1, -1, -2, -3, -4, -4,
    -1, -4, -1, -2]

@[expose] def onBWord : List Int :=
  [2, 1, 4, 2, 2, 1, 3, 1, -3, 2, 4, 4, 4, 4, 4, 4, 2, 3, -4, 1, 4, -3, 4, 4, 2, 3, -4, 1, 4,
    -3, 2, 3, -4, 1, 3, 4, -2, -2, -4, 3, 4, 3, 4, 3, 4, 3, 4]

@[expose, irreducible] def onTArrs : Array (Array Nat) := wordArrs Data.TWords

@[expose, irreducible] def onTInvArrs : Array (Array Nat) := pinvs nPts onTArrs

@[expose] def onE8Arr (j k : Nat) : Array Nat :=
  pword nPts onTArrs onTInvArrs (onE8Words[j]!)[k]!

@[expose, irreducible] def onNormArrs : Array (Array Nat) := onNormWords.map wordArr

@[expose, irreducible] def onNormInvArrs : Array (Array Nat) := pinvs nPts onNormArrs

@[expose] def pinvol (x : Array Nat) : Bool := peq nPts (pcomp nPts x x) (pid nPts)

@[expose] def pcommute (x y : Array Nat) : Bool := peq nPts (pcomp nPts x y) (pcomp nPts y x)

@[expose] def pelems4 (x y : Array Nat) : List (Array Nat) := [pid nPts, x, y, pcomp nPts x y]

@[expose] def pelems8 (x y z : Array Nat) : List (Array Nat) :=
  pelems4 x y ++ (pelems4 x y).map fun f => pcomp nPts f z

@[expose] def pe8OK (x y z : Array Nat) : Bool :=
  pinvol x && pinvol y && pinvol z && pcommute x y && pcommute x z && pcommute y z &&
    !peq nPts x (pid nPts) && !peq nPts y (pid nPts) && !peq nPts y x &&
    (pelems4 x y).all fun f => !peq nPts z f

@[expose] def pnormOK (n ninv x y z : Array Nat) : Bool :=
  [x, y, z].all fun e =>
    (pelems8 x y z).any fun f => peq nPts (pcomp nPts (pcomp nPts n e) ninv) f

@[expose] def onEightNormalizersCheck : Bool :=
  onTArrs.size == 6 && allBelowN 6 (fun h => pisInv nPts onTArrs[h]! onTInvArrs[h]!) &&
    onNormArrs.size == 4 &&
    allBelowN 4 (fun i => pisInv nPts onNormArrs[i]! onNormInvArrs[i]!) &&
    pe8OK (onE8Arr 0 0) (onE8Arr 0 1) (onE8Arr 0 2) &&
    pe8OK (onE8Arr 1 0) (onE8Arr 1 1) (onE8Arr 1 2) &&
    allBelowN 4 (fun i => pnormOK onNormArrs[i]! onNormInvArrs[i]!
      (onE8Arr onNormTags[i]! 0) (onE8Arr onNormTags[i]! 1) (onE8Arr onNormTags[i]! 2)) &&
    peq nPts (pword nPts onNormArrs onNormInvArrs onAWord) (wordArr [1]) &&
    peq nPts (pword nPts onNormArrs onNormInvArrs onBWord) (wordArr [2])

end CFSG.ONSchreier

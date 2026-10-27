module

public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.Sporadic.Schreier.Co3.Native

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def hexLine (b : ByteArray) (w n L : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => hexAt b (L * (w * n + 1) + w * i.val) w

@[expose] def layoutOK (b : ByteArray) (w n m : Nat) : Bool :=
  b.size == m * (w * n + 1) && allLt m fun L => b.get! (L * (w * n + 1) + w * n) == 10

@[expose] def wordsArr (k s : Nat) (D : List (List Int)) : Array (List Int) :=
  Array.ofFn (n := s) fun j => if j.val < k then [] else D.getD (j.val - k) []

@[expose] def wordsOK (k s : Nat) (D : List (List Int)) : Bool :=
  D.length + k == s && allLt s fun j => decide (j < k) || lettersOK j (wordsArr k s D)[j]!

@[expose] def permsOK (n : Nat) (A : Array (Array Nat)) : Bool :=
  allLt A.size fun j => isInvA n A[j]! (invCand n A[j]!)

@[expose] def posIn (I : Array Nat) (p : Nat) : Nat :=
  (I.findIdx? (· == p)).getD I.size

@[expose] def restrictA (I : Array Nat) (m : Array Nat) : Array Nat :=
  Array.ofFn (n := I.size) fun i => posIn I m[I[i.val]!]!

@[expose] def renameA (k : Nat) (c π : Array Nat) : Array Nat :=
  compA k (compA k c π) (invCand k c)

@[expose] def preservesOK (I : Array Nat) (m : Array Nat) : Bool :=
  allLt I.size fun i => decide (posIn I m[I[i]!]! < I.size)

@[inline, expose] def anyLt (n : Nat) (p : Nat → Bool) : Bool := Nat.any n fun i _ => p i

@[expose] def coversOK (n : Nat) (gs hs : Array (Array Nat)) : Bool :=
  (allLt gs.size fun i => eqA n gs[i]! (idA n) || anyLt hs.size fun j => eqA n gs[i]! hs[j]!) &&
    allLt hs.size fun j => anyLt gs.size fun i => eqA n hs[j]! gs[i]!

@[expose] def commA (n : Nat) (gs : Array (Array Nat)) (i j : Nat) : Array Nat :=
  compA n (compA n (compA n gs[j]! gs[i]!) (invCand n gs[j]!)) (invCand n gs[i]!)

@[inline, expose] def commutesA (n : Nat) (t u : Array Nat) : Bool :=
  eqA n (compA n t u) (compA n u t)

@[expose] def centerCheck3 (n : Nat) (L : Array Level) (gens : Array (Array Nat))
    (z : Array Nat) : Bool :=
  allLt L[0]!.pts.size fun a => allLt L[1]!.pts.size fun b => allLt L[2]!.pts.size fun c =>
    let g := compA n (compA n L[0]!.tr[a]! L[1]!.tr[b]!) L[2]!.tr[c]!
    !(allLt gens.size fun k => commutesA n g gens[k]!) || eqA n g (idA n) || eqA n g z

end CFSG.Sporadic.Schreier.Co3.Native

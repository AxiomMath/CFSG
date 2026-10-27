
module

public import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckBase
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.LocalCheckBase

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.Sporadic.He.Native CFSG.ONSchreier.Native

@[expose] def initRegsM (A B : Array (Array Nat)) : Array (Array (Array Nat)) :=
  #[idM 133, A, B] ++ Array.replicate 8 (idM 133)

@[expose] def progRegsM (regs : Array (Array (Array Nat))) :
    List (Nat × Nat × Nat) → Array (Array (Array Nat))
  | [] => regs
  | (a, b, c) :: rest => progRegsM (regs.set! c (mulM 5 133 regs[a]! regs[b]!)) rest

@[expose] def mletter (S Si : Array (Array (Array Nat))) (l : Int) : Array (Array Nat) :=
  if 0 < l then S[l.toNat - 1]! else Si[(-l).toNat - 1]!

@[expose] def mword (S Si : Array (Array (Array Nat))) : List Int → Array (Array Nat)
  | [] => idM 133
  | l :: w => mulM 5 133 (mletter S Si l) (mword S Si w)

@[expose] def extendStrongM (orig : Array (Array (Array Nat))) (W : Array (List Int)) :
    Array (Array (Array Nat)) × Array (Array (Array Nat)) := Id.run do
  let mut S := orig
  let mut Si := orig.map (invM 5 133)
  for j in [orig.size:W.size] do
    let s := mword S Si W[j]!
    S := S.push s
    Si := Si.push (invM 5 133 s)
  return (S, Si)

@[expose] def strongOKM (A0 A1 : Array (Array Nat)) (S Si : Array (Array (Array Nat)))
    (W : Array (List Int)) : Bool :=
  2 ≤ W.size && S.size == W.size && Si.size == W.size && S[0]! == A0 && S[1]! == A1 &&
    allBelowN S.size (fun j => mulM 5 133 S[j]! Si[j]! == idM 133) &&
    allBelowN S.size (fun j => decide (j < 2) ||
      (plettersOK j W[j]! && S[j]! == mword S Si W[j]!))

@[expose] def rootVec : Array Nat :=
  Array.ofFn (n := 133) fun j => (Data.rootDigits.toList.getD j.val '0').toNat - '0'.toNat

@[expose] def seedWordVec (A B : Array (Array Nat)) (w : List Nat) (v : Array Nat) : Array Nat :=
  w.foldr (fun l y => mulVec 5 133 (seedSel A B l) y) v

@[expose] def xVecs (H : Array (Array (Array Nat))) (x0 : Array Nat) (recs : List (Nat × Nat)) :
    Array (Array Nat) :=
  (recs.drop 1).foldl (fun acc r => acc.push (mulVec 5 133 H[r.2 - 1]! acc[r.1]!)) #[x0]

@[expose] def tauArr : Array Nat := #[1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

@[expose] def tauIdx : Array Nat :=
  Array.ofFn (n := 462) fun i =>
    (labMasks.findIdx? (· == canonMask (permMask tauArr labMasks[i.val]!))).getD 0

@[noinline, expose] def involChecks (A B S C : Array (Array Nat)) (tau M : Array Nat) : Bool :=
  let regs := progRegsM (initRegsM A B) Data.subgroupProgram
  let h1 := regs[1]!
  let h2 := regs[2]!
  let hs := extendStrongM #[h1, h2] LocalData.strongWords
  let H := hs.1
  let Hi := hs.2
  let D := mword H Hi LocalData.innerWord
  let U := wordM (seedSel A B) LocalData.outerWord
  let Ui := invM 5 133 U
  let W := powM 5 133 (mulM 5 133 A (mulM 5 133 B B)) 8
  let v := rootVec
  let x0 := seedWordVec A B LocalData.rootWord v
  let xs := xVecs H x0 LocalData.parents
  regs.size == 11 && strongOKM h1 h2 H Hi LocalData.strongWords &&
    mulM 5 133 U Ui == idM 133 && mulM 5 133 (mulM 5 133 D Ui) S == C &&
    mulM 5 133 C C == idM 133 && notIdM 133 C && mulVec 5 133 C v == v &&
    mulM 5 133 S A == mulM 5 133 A S &&
    mulM 5 133 W (mulM 5 133 S B) == mulM 5 133 B (mulM 5 133 W S) &&
    xs.size == 462 && xs[0]! == x0 &&
    allBelowN 462 (fun i => i == 0 || xs[i]! ==
      mulVec 5 133 H[LocalData.parents[i]!.2 - 1]! xs[LocalData.parents[i]!.1]!) &&
    tau.size == 462 &&
    allBelowN 462 (fun i => decide (tau[i]! < 462) &&
      M[tau[i]!]! == canonMask (permMask tauArr M[i]!) &&
      mulVec 5 133 C xs[i]! == xs[tau[i]!]!)

end CFSG.Sporadic.HNSchreier.Native

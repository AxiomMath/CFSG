module

public import CFSG.Sporadic.ONOddCore.LocalAutPayload

public section

namespace CFSG.Sporadic.ONOddCore

inductive Cand where
  | lift (i : Nat)
  | rel (w w' : List Nat)
deriving Inhabited

structure LiftData where
  qWord : List Nat
  lw : List (List (List Nat))
  cands : List (List Cand)
deriving Inhabited

@[expose] def liftsText : String := include_str "Data"/"lifts.txt"

@[expose] def readCand (xs : List Nat) : Cand × List Nat :=
  match xs with
  | 0 :: i :: ys => (.lift i, ys)
  | _ :: ys =>
    let (w, ys) := readWord ys
    let (w', ys) := readWord ys
    (.rel w w', ys)
  | [] => (default, [])

@[expose] def readMany {α : Type} (rd : List Nat → α × List Nat) :
    Nat → List Nat → List α × List Nat
  | 0, xs => ([], xs)
  | k + 1, xs =>
    let (a, ys) := rd xs
    let (as, zs) := readMany rd k ys
    (a :: as, zs)

@[expose] def decodeLifts (xs : List Nat) : LiftData :=
  let (q, ys) := readWord xs
  let (lw, ys) := readMany (readMany readWord 3) 12 ys
  let (cs, _) := readMany (readMany readCand 64) 12 ys
  ⟨q, lw, cs⟩

@[expose] def liftData : LiftData := decodeLifts (natsOf liftsText)

end CFSG.Sporadic.ONOddCore

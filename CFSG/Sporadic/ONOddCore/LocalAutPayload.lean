module


public section

namespace CFSG.Sporadic.ONOddCore

structure LiftEntry where
  power : Nat
  words : List (List Nat)
deriving Inhabited

structure QuotRecord where
  diag : Nat
  field : Nat
  graph : Nat
  images : List (Array Nat)
  lifts : List LiftEntry
deriving Inhabited

structure LocalCert where
  quotGens : List (Array Nat)
  records : List QuotRecord
deriving Inhabited

@[expose] def localAutText : String := include_str "Data"/"localaut.txt"

@[expose] def natsOf (s : String) : List Nat :=
  (((s.splitOn "\n").flatMap fun l => l.splitOn " ").filter fun w => !w.isEmpty).map String.toNat!

@[expose] def readN (k : Nat) (xs : List Nat) : List Nat × List Nat := (xs.take k, xs.drop k)

@[expose] def readWord (xs : List Nat) : List Nat × List Nat :=
  match xs with
  | [] => ([], [])
  | k :: ys => readN k ys

@[expose] def readLift (xs : List Nat) : LiftEntry × List Nat :=
  match xs with
  | [] => (default, [])
  | p :: ys =>
    let (w₁, ys) := readWord ys
    let (w₂, ys) := readWord ys
    let (w₃, ys) := readWord ys
    (⟨p, [w₁, w₂, w₃]⟩, ys)

@[expose] def readLifts : Nat → List Nat → List LiftEntry × List Nat
  | 0, xs => ([], xs)
  | k + 1, xs =>
    let (e, ys) := readLift xs
    let (es, zs) := readLifts k ys
    (e :: es, zs)

@[expose] def readRecord (xs : List Nat) : QuotRecord × List Nat :=
  match xs with
  | d :: f :: g :: ys =>
    let (a₁, ys) := readN 120 ys
    let (a₂, ys) := readN 120 ys
    match ys with
    | [] => (⟨d, f, g, [a₁.toArray, a₂.toArray], []⟩, [])
    | k :: zs =>
      let (ls, zs) := readLifts k zs
      (⟨d, f, g, [a₁.toArray, a₂.toArray], ls⟩, zs)
  | _ => (default, [])

@[expose] def readRecords : Nat → List Nat → List QuotRecord
  | 0, _ => []
  | k + 1, xs =>
    let (r, ys) := readRecord xs
    r :: readRecords k ys

@[expose] def decodeCert (xs : List Nat) : LocalCert :=
  let (a₁, ys) := readN 120 xs
  let (a₂, ys) := readN 120 ys
  ⟨[a₁.toArray, a₂.toArray], readRecords 12 ys⟩

@[expose] def localCert : LocalCert := decodeCert (natsOf localAutText)

end CFSG.Sporadic.ONOddCore

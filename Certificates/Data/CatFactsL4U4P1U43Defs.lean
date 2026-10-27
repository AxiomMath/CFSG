module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1UAction
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Check
public import CFSG.LieType.Multipliers.U43Bridge
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43

open CFSG.LieType.Multipliers.U43 CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Native
  CFSG.Monster.B.Co2.Native

@[expose] def matN9 (k : ℕ) : Matrix (Fin 4) (Fin 4) F9 :=
  Matrix.of fun i j => uncode (k / 9 ^ (4 * i.val + j.val) % 9)

@[expose] def tu (k : ℕ) (ε : Bool) : Table :=
  let A := matN9 k
  Array.ofFn (n := 820) fun i =>
    UInt32.ofNat (ptIndex (mv4 A (if ε then barV (decode i.val) else decode i.val)))

@[expose] def codeDm1 : ℕ := 6 + 3 * 9 ^ 5 + 3 * 9 ^ 10 + 3 * 9 ^ 15

@[expose] def uPg : Array Table := #[toTable tabA, toTable tabB]

@[expose] def uBase : Array ℕ := (chainBase.map Fin.val).toArray

@[expose] def uLevels : Array Level := rawLevels 820 chainS uBase

@[expose] def uSift (T : Table) : Bool := siftA 820 uLevels uBase 0 (natArr T)

@[expose] def bfsPairs (n : Nat) (gens : Array Table) (bases : List (Nat × Table × Table)) :
    Array (Table × Table) := Id.run do
  let gensInv := gens.map (invT n)
  let mut res : Array (Option (Table × Table)) := Array.replicate n none
  let mut queue : Array Nat := #[]
  for b in bases do
    res := res.set! b.1 (some b.2)
    queue := queue.push b.1
  for h in [0:n] do
    if h < queue.size then
      let p := queue[h]!
      match res[p]! with
      | some (h₁, h₂) =>
        for l in [0:gens.size] do
          let q := ap gens[l]! p
          if res[q]!.isNone then
            res := res.set! q (some (conjT n gens[l]! gensInv[l]! h₁,
              conjT n gens[l]! gensInv[l]! h₂))
            queue := queue.push q
      | none => pure ()
  return res.map (·.getD default)

end CFSG.ComponentClassification.HarrisLit.P1.U43

module

public import CFSG.Monster.B.TwoA.Unitary.TwentyData
public import CFSG.Monster.Code.Bits
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public meta import CFSG.Monster.B.TwoA.Unitary.TwentyData
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.AbsolutelyIrreducible
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.JacobsonDensity
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

public section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster.Code

@[expose] def actGoR (rows : Array ℕ) (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => actGoR rows c n ^^^ (if c.testBit n then rows[n]! else 0)

@[expose] def actR (rows : Array ℕ) (c : ℕ) : ℕ := actGoR rows c 20

@[expose] def rowsMul (A B : Array ℕ) : Array ℕ :=
  ((List.range 20).map fun t => actR B A[t]!).toArray

@[expose] def rowsXor (A B : Array ℕ) : Array ℕ :=
  ((List.range 20).map fun t => A[t]! ^^^ B[t]!).toArray

@[expose] def idRows : Array ℕ := ((List.range 20).map fun t => 1 <<< t).toArray

@[expose] def zeroRows : Array ℕ := ((List.range 20).map fun _ => 0).toArray

@[expose] def wordRows : List ℕ → Array ℕ
  | [] => idRows
  | k :: w => rowsMul u20Gens[k]! (wordRows w)

@[expose] def flatRows (M : Array ℕ) : ℕ :=
  (List.range 20).foldl (fun acc i => acc ||| (M[i]! <<< (20 * i))) 0

@[expose] def gaussInv (n : ℕ) (rows : Array ℕ) : Array ℕ := Id.run do
  let mut A : Array (ℕ × ℕ) := ((List.range n).map fun i => (rows[i]!, 1 <<< i)).toArray
  for c in [0:n] do
    let mut p := n
    for r in [c:n] do
      if p == n && (A[r]!.1.testBit c) then p := r
    if p < n then
      let tmp := A[c]!
      A := (A.set! c A[p]!).set! p tmp
      for r in [0:n] do
        if r != c && (A[r]!.1.testBit c) then
          A := A.set! r (A[r]!.1 ^^^ A[c]!.1, A[r]!.2 ^^^ A[c]!.2)
  return A.map (·.2)

@[expose] def unitCert : Array ℕ := gaussInv 400 (u20RecRows.map flatRows)

@[expose] def combRows (s : ℕ) : Array ℕ :=
  (List.range 400).foldl (fun acc j => if s.testBit j then rowsXor acc u20RecRows[j]! else acc)
    zeroRows

@[expose] def eRows (c : ℕ) : Array ℕ :=
  ((List.range 20).map fun i => if i = c / 20 then 1 <<< (c % 20) else 0).toArray

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (b : Module.Basis (Fin 20) (ZMod 2) V)

end CFSG.Monster.B.TwoA.Unitary

module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.Common.Eval

namespace CertificateChecks.KernelCo1ThreeK.GenC

open CFSG.KC.Eval

meta def nats : Val → Except String (Array Nat)
  | .list xs => xs.mapM fun | .nat n => pure n | _ => throw "cStep: expected a natural"
  | _ => throw "cStep: expected a list"

meta def natss : Val → Except String (Array (Array Nat))
  | .list xs => xs.mapM nats
  | _ => throw "cStep: expected a list of lists"

meta def natsV (xs : Array Nat) : Val := .list (xs.map .nat)

meta def addV (x y : Nat) : Nat := Id.run do
  let mut r := 0
  let mut x := x
  let mut y := y
  let mut b := 1
  for _ in [0:6] do
    r := r + b * ((x % 3 + y % 3) % 3)
    x := x / 3
    y := y / 3
    b := b * 3
  return r

meta def actV (rows : Array Nat) (v acc : Nat) : Nat := Id.run do
  let mut acc := acc
  let mut v := v
  for j in [0:rows.size] do
    for _ in [0:v % 3] do
      acc := addV acc rows[j]!
    v := v / 3
  return acc

meta def free (R B : Array Nat) : Bool :=
  (List.range (3 ^ B.size - 1)).all fun a =>
    let c := actV B (a + 1) 0
    actV R c 0 != c

meta def basis (R : Array Nat) (m : Nat) : Option (Array Nat) := Id.run do
  let mut B : Array Nat := #[]
  for c in [1:729] do
    if B.size < m && free R (B.push c) then
      B := B.push c
  return if B.size == m then some B else none

meta def nFix (R : Array Nat) : Nat := ((List.range 729).filter fun u => actV R u 0 == u).length

public meta def cStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 1 then throw "cStep: expected CS.TR"
  let A ← natss args[0]!
  if A.size != 27 then throw "cStep: expected 27 actions"
  let mut B : Array Val := #[]
  for l in [1:27] do
    let some b := basis A[l]! 3 | throw s!"cStep: coset {l} fixes more than 27 codes"
    B := B.push (natsV b)
  let some l0 := (List.range 26).find? (fun l => nFix A[l + 1]! ≤ 9) |
    throw "cStep: no coset fixes at most 9 codes"
  let some b0 := basis A[l0 + 1]! 4 | throw "cStep: basis of 4"
  return #[(`B, .list B), (`K0, .nat (l0 + 1)), (`B0, natsV b0)]

end CertificateChecks.KernelCo1ThreeK.GenC

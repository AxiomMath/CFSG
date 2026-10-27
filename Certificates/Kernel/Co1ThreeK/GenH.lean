module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.Common.Eval

namespace CertificateChecks.KernelCo1ThreeK.Gen

open CFSG.KC.Eval

meta def addH (x y : Nat) : Nat := Id.run do
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

meta def actH (rows : Array Nat) (v : Nat) : Nat := Id.run do
  let mut acc := 0
  let mut v := v
  for r in rows do
    for _ in [0:v % 3] do
      acc := addH acc r
    v := v / 3
  return acc

meta def natsH : Val → Except String (Array Nat)
  | .list xs => xs.mapM fun
    | .nat n => pure n
    | _ => throw "hStep: expected a natural"
  | _ => throw "hStep: expected a list"

meta def dotV (x y : Nat) : Nat := Id.run do
  let mut r := 0
  let mut x := x
  let mut y := y
  for _ in [0:6] do
    r := (r + (x % 3) * (y % 3)) % 3
    x := x / 3
    y := y / 3
  return r

meta def dualRows (m : Array Nat) : Except String (Array Nat) := do
  let mut d : Array Nat := #[]
  for j in [0:6] do
    let mut found : Option Nat := none
    for c in [0:729] do
      if found.isNone && (List.range 6).all fun i => dotV m[i]! c == (if i == j then 1 else 0) then
        found := some c
    let some c := found | throw "hStep: singular rows"
    d := d.push c
  return d

public meta def hStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[.list nr] := args | throw "hStep: expected the rows NR"
  if nr.size < 3 then throw "hStep: expected at least 3 normalizers"
  let ms ← (nr.extract 0 3).mapM natsH
  let ds ← ms.mapM dualRows
  let roots : List Nat := [243, 81, 190]
  let mut ft : Array Nat := Array.replicate 729 0
  let mut dp : Array Nat := Array.replicate 729 0
  let mut seen : Array Bool := Array.replicate 729 false
  let mut queue : Array Nat := #[]
  for r in roots do
    seen := seen.set! r true
    queue := queue.push r
  let mut i := 0
  while i < queue.size do
    let pc := queue[i]!
    for g in [0:3] do
      let c := actH ds[g]! pc
      if !seen[c]! then
        seen := seen.set! c true
        ft := ft.set! c (pc + 729 * g)
        dp := dp.set! c (dp[pc]! + 1)
        queue := queue.push c
    i := i + 1
  if queue.size != 728 then throw s!"hStep: the roots reach {queue.size} codes"
  if dp.any (· > 255) then throw "hStep: depth above 255"
  let mut dpN := 0
  for c in [0:729] do
    dpN := dpN + dp[c]! * 2 ^ (8 * c)
  return #[(`DR, .list (ds.map fun d => .list (d.map .nat))),
    (`RT, .list (roots.toArray.map .nat)),
    (`FT, .list ((ft.extract 1 729).map .nat)),
    (`DP, .nat dpN)]

end CertificateChecks.KernelCo1ThreeK.Gen

module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.Common.Eval

namespace CertificateChecks.KernelCo1ThreeK.Gen

open CFSG.KC.Eval

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

meta def actV (rows : Array Nat) (v : Nat) : Nat := Id.run do
  let mut acc := 0
  let mut v := v
  for r in rows do
    for _ in [0:v % 3] do
      acc := addV acc r
    v := v / 3
  return acc

meta def natsOf : Val → Except String (Array Nat)
  | .list xs => xs.mapM fun
    | .nat n => pure n
    | _ => throw "fStep: expected a natural"
  | _ => throw "fStep: expected a list"

public meta def fStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let #[.list nr] := args | throw "fStep: expected the rows NR"
  if nr.size < 3 then throw "fStep: expected at least 3 normalizers"
  let ms ← (nr.extract 0 3).mapM natsOf
  let roots : List Nat := [81, 243, 327]
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
      let c := actV ms[g]! pc
      if !seen[c]! then
        seen := seen.set! c true
        ft := ft.set! c (pc + 729 * g)
        dp := dp.set! c (dp[pc]! + 1)
        queue := queue.push c
    i := i + 1
  if queue.size != 728 then throw s!"fStep: the roots reach {queue.size} codes"
  if dp.any (· > 255) then throw "fStep: depth above 255"
  let mut dpN := 0
  for c in [0:729] do
    dpN := dpN + dp[c]! * 2 ^ (8 * c)
  return #[(`RT, .list (roots.toArray.map .nat)),
    (`FT, .list ((ft.extract 1 729).map .nat)),
    (`DP, .nat dpN)]

end CertificateChecks.KernelCo1ThreeK.Gen

module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.Common.Eval

namespace CertificateChecks.KernelAP

open CFSG.KC.Eval

meta def par (n : Nat) : Nat := Id.run do
  let mut p := 0
  for j in [0:24] do
    p := p ^^^ ((n >>> j) &&& 1)
  return p

meta def vecOps (ops : Array (Nat × Nat)) (v : Nat) : Nat :=
  ops.foldl (fun v (t, l) => v ^^^ (par (l &&& v) <<< t)) v

meta def solve (col : Array Nat) (target : Nat) : Except String Nat := do
  let mut basis : Array (Option (Nat × Nat)) := Array.replicate 24 none
  for j in [0:24] do
    let mut v := col[j]!
    let mut comb := 1 <<< j
    let mut b := 24
    while b > 0 do
      b := b - 1
      if (v >>> b) &&& 1 == 1 then
        match basis[b]! with
        | some (bv, bc) => v := v ^^^ bv; comb := comb ^^^ bc
        | none => basis := basis.set! b (some (v, comb)); b := 0
  let mut v := target
  let mut comb := 0
  let mut b := 24
  while b > 0 do
    b := b - 1
    if (v >>> b) &&& 1 == 1 then
      match basis[b]! with
      | some (bv, bc) => v := v ^^^ bv; comb := comb ^^^ bc
      | none => throw "solve: singular"
  return comb

meta def decomposeFrom (rows : Array Nat) (seed0 : Nat) : Except String (Array (Nat × Nat)) := do
  let mut col : Array Nat := Array.ofFn (n := 24) fun c =>
    (List.range 24).foldl (fun acc r => acc ||| (((rows[r]! >>> c.val) &&& 1) <<< r)) 0
  let mut ops : Array (Nat × Nat) := #[]
  let mut done : Array Bool := Array.replicate 24 false
  let mut seed : Nat := seed0
  let mut guard := 0
  while done.any (· == false) do
    guard := guard + 1
    if guard > 5000 then throw "decompose: no progress"
    let mut progress := false
    for t in [0:24] do
      if done[t]! then continue
      if col[t]! == 1 <<< t then
        done := done.set! t true
        progress := true
        continue
      let a ← solve col ((1 <<< t) ^^^ col[t]!)
      if (a >>> t) &&& 1 == 0 then
        let mut c := col[t]!
        for j in [0:24] do
          if (a >>> j) &&& 1 == 1 then c := c ^^^ col[j]!
        col := col.set! t c
        ops := ops.push (t, a)
        done := done.set! t true
        progress := true
    if !progress then
      let t := (List.range 24).find? (fun k => !done[k]!) |>.getD 0
      seed := (seed * 6364136223846793005 + 1442695040888963407) % 18446744073709551616
      let j0 := (seed >>> 33) % 23
      let j := if j0 < t then j0 else j0 + 1
      col := col.set! t (col[t]! ^^^ col[j]!)
      ops := ops.push (t, 1 <<< j)
  let seq := ops.reverse
  for j in [0:24] do
    if vecOps seq (1 <<< j) != rows[j]! then throw "decompose: wrong factorisation"
  return seq

meta def decompose (rows : Array Nat) : Except String (Array (Nat × Nat)) := do
  let mut best ← decomposeFrom rows 1
  for s in [2:65] do
    if best.size ≤ 24 then break
    let ops ← decomposeFrom rows s
    if ops.size < best.size then best := ops
  return best

@[noinline] meta def bitPl (ones j : Nat) : Nat :=
  (((1 <<< (1 <<< j)) - 1) <<< (1 <<< j)) * (ones / ((1 <<< (1 <<< (j + 1))) - 1))

meta def masksOf (ones : Nat) (bits : Array Nat) (ops : Array (Nat × Nat)) : Array (Nat × Nat) :=
  ops.map fun (t, l) =>
    let p := (List.range 24).foldl
      (fun acc j => if (l >>> j) &&& 1 == 1 then acc ^^^ bits[j]! else acc) 0
    (1 <<< t, p &&& (ones ^^^ bits[t]!))

meta def applyM (ms : Array (Nat × Nat)) (S : Nat) : Nat :=
  ms.foldl (fun S (d, m) => let u := ((S >>> d) ^^^ S) &&& m; S ^^^ u ^^^ (u <<< d)) S

meta def popW (ones S : Nat) : Nat := Id.run do
  let mut y := S
  for s in [0:5] do
    let w := 1 <<< s
    let m := ((1 <<< w) - 1) * (ones / ((1 <<< (2 * w)) - 1))
    y := (y &&& m) + ((y >>> w) &&& m)
  return y % 4294967295

meta def salted (k S : Nat) : Nat :=
  (S <<< 64) ||| (((k + 1) * 11400714819323198485 + 977) % 18446744073709551616)

meta def natList (v : Val) : Except String (Array Nat) := do
  match v with
  | .list xs => xs.mapM fun x => match x with
    | .nat n => pure n
    | _ => throw "planeStep: expected a list of numbers"
  | _ => throw "planeStep: expected a list"

public meta def planeStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size < 2 then throw "planeStep: expected the points and the matrices"
  let lams ← natList args[0]!
  let mut opsAll : Array (Array (Nat × Nat)) := #[]
  for a in args.extract 1 args.size do
    let rows ← natList a
    if rows.size != 24 then throw "planeStep: a matrix needs 24 rows"
    opsAll := opsAll.push (← decompose rows)
  let n := lams.size
  let nl := (Nat.log2 n) + 1
  let N := if args.size > 1000 then 0 else 1 <<< 24
  let ones := (1 <<< N) - 1
  let bits := Array.ofFn (n := 24) fun j => bitPl ones j.val
  let mss := opsAll.map (masksOf ones bits)
  let mut V := 0
  let mut L : Array Nat := Array.replicate nl 0
  for r in [0:n] do
    let x := lams[r]!
    if x ≥ N || V.testBit x then throw s!"planeStep: point {r} repeated or too large"
    V := V ||| (1 <<< x)
    for b in [0:nl] do
      if ((r + 1) >>> b) &&& 1 == 1 then L := L.modify b (· ||| (1 <<< x))
  let mut Q : Array Nat := Array.replicate 5 0
  Q := Q.set! 0 V
  let mut F := V
  let mut T := 1
  for _ in [0:40] do
    let mut NF := 0
    let mut NL : Array Nat := Array.replicate nl 0
    for ms in mss do
      NF := NF ||| applyM ms F
      for b in [0:nl] do
        NL := NL.modify b (· ||| applyM ms (L[b]! &&& F))
    NF := NF &&& (ones ^^^ V)
    if NF == 0 then break
    T := T + 1
    if T ≥ 32 then throw "planeStep: more than 31 levels"
    V := V ||| NF
    F := NF
    for b in [0:nl] do
      L := L.modify b (· ||| (NL[b]! &&& NF))
    for j in [0:5] do
      if (T >>> j) &&& 1 == 1 then Q := Q.modify j (· ||| NF)
  let mut outs : Array (Lean.Name × Val) := #[]
  for g in [0:opsAll.size] do
    outs := outs.push (Lean.Name.mkSimple s!"ops{g}",
      .list (opsAll[g]!.map fun (t, l) => .nat (t + 32 * l)))
  outs := outs.push (`opss, .list ((Array.range opsAll.size).map fun g =>
    .ref (Lean.Name.mkSimple s!"ops{g}")))
  for b in [0:nl] do
    outs := outs.push (Lean.Name.mkSimple s!"L{b}", .nat (salted (1000 + b) L[b]!))
  for j in [0:5] do
    outs := outs.push (Lean.Name.mkSimple s!"Q{j}", .nat (salted (2000 + j) Q[j]!))
  for g in [0:opsAll.size] do
    for j in [0:5] do
      outs := outs.push (Lean.Name.mkSimple s!"R{g}_{j}",
        .nat (salted (3000 + 8 * g + j) (applyM mss[g]! Q[j]!)))
    outs := outs.push (Lean.Name.mkSimple s!"Rs{g}",
      .list ((Array.range 5).map fun j => .ref (Lean.Name.mkSimple s!"R{g}_{j}")))
  outs := outs.push (`Rss, .list ((Array.range opsAll.size).map fun g =>
    .ref (Lean.Name.mkSimple s!"Rs{g}")))
  outs := outs.push (`Ls, .list ((Array.range nl).map fun b => .ref (Lean.Name.mkSimple s!"L{b}")))
  outs := outs.push (`Qs, .list ((Array.range 5).map fun j => .ref (Lean.Name.mkSimple s!"Q{j}")))
  outs := outs.push (`T, .nat T)
  outs := outs.push (`found, .nat (popW ones V))
  return outs

end CertificateChecks.KernelAP

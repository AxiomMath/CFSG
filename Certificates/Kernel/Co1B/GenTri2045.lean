module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.KS.GenTri

meta def packM (R : Array Nat) : Nat := CFSG.KS.RawGen.pack 24 R

meta def trR (R : Array Nat) : Array Nat :=
  Array.ofFn (n := 24) fun j => (List.range 24).foldl
    (fun acc i => if (R.getD i 0).testBit j.val then acc ||| (1 <<< i) else acc) 0

meta def actR (R : Array Nat) (v : Nat) : Nat :=
  (List.range 24).foldl (fun acc i =>
    let c := R.getD i 0 &&& v
    let par := (List.range 24).foldl (fun s b => if c.testBit b then !s else s) false
    if par then acc ||| (1 <<< i) else acc) 0

meta def mulR (X Y : Array Nat) : Array Nat :=
  X.map fun r => (List.range 24).foldl (fun acc j => if r.testBit j then acc ^^^ Y.getD j 0 else acc) 0

meta def swaps (p : Array Nat) : Array Nat := Id.run do
  let n := p.size
  let mut q := p
  let mut inv : Array Nat := Array.replicate n 0
  for i in [0:n] do
    inv := inv.set! q[i]! i
  let mut out : Array Nat := #[]
  for i in [0:n] do
    if q[i]! != i then
      let b := inv[i]!
      let qi := q[i]!
      q := (q.set! i i).set! b qi
      inv := (inv.set! i i).set! qi b
      out := (out.push i).push b
  return out

end CFSG.KS.GenTri

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.GenTri in
elab "#kss_co1tri " pre:ident tId:ident d1Id:ident d2Id:ident : command => do
  let get := fun (i : Ident) => liftCoreM <| realizeGlobalConstNoOverload i
  let T ← liftTermElabM <| unsafe evalConst (List (Nat × Nat)) (← get tId)
  let D1 ← liftTermElabM <| unsafe evalConst (List (Array Nat) × List (Array Nat) × Bool) (← get d1Id)
  let D2 ← liftTermElabM <| unsafe evalConst (List (Array Nat) × List (Array Nat) × Bool) (← get d2Id)
  let P := pre.getId
  let n := T.length
  if n != 1365 then throwError "{n} triples"
  let Ta := T.toArray
  let vec := fun (i : Nat) =>
    let p := Ta[i / 3]!
    if i % 3 == 0 then p.1 else if i % 3 == 1 then p.2 else p.1 ^^^ p.2
  let idx : Std.HashMap Nat Nat := (List.range 4095).foldl (fun m i => m.insert (vec i) (i / 3)) {}
  if idx.size != 4095 then throwError "vectors not distinct"
  let PT := pack 24 (Ta.foldl (fun a p => (a.push p.1).push p.2) #[])
  let order := (Array.range 4095).qsort fun x y => vec x < vec y
  let SV := order.map vec
  let mut rk : Array Nat := Array.replicate 4095 0
  for r in [0:4095] do
    rk := rk.set! order[r]! r
  let aRr := D1.1.getD 0 #[]
  let mats : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 19, 21]
  let rows := fun (j : Nat) => D2.1.getD j #[]
  let perm := fun (R : Array Nat) => Id.run do
    let mut out : Array Nat := #[]
    for k in [0:n] do
      out := out.push (idx.getD (actR R Ta[k]!.1) n)
    return out
  let mut Ts : Array Nat := #[]
  let mut Ps : Array Nat := #[]
  let mut PIs : Array Nat := #[]
  let mut perms : Array (Array Nat) := #[]
  for j in mats do
    let R := rows j
    let p := perm R
    for k in [0:n] do
      let q := Ta[k]!
      if idx.getD (actR R q.2) n != p[k]! || idx.getD (actR R (q.1 ^^^ q.2)) n != p[k]! then
        throwError "entry {j} does not map triple {k} onto a triple"
    perms := perms.push p
    Ts := Ts.push (packM (trR R))
    Ps := Ps.push (pack 11 p)
    PIs := PIs.push (pack 11 (inv n p))
  Ts := Ts.push (packM (trR aRr))
  let sw := #[swaps perms[10]!, swaps perms[11]!, swaps perms[5]!]
  let mut p15 := perms[2]!
  for _ in [0:14] do
    p15 := comp n p15 perms[2]!
  if p15 != Array.range n then throwError "the entry 2 does not have order dividing 15 on the triples"
  if rows 3 != aRr then throwError "the entry 3 is not A₁"
  let mut Z := rows 2
  for _ in [0:14] do
    Z := mulR Z (rows 2)
  let find := fun (f : Nat → Bool) => ((List.range 24).find? fun i => f (1 <<< i)).map (1 <<< ·)
  let some v0 := find fun v => actR aRr v != v | throwError "A₁ = 1"
  let some v1 := find fun v => actR Z v != v | throwError "z = 1"
  let some v2 := find fun v => actR Z v != actR aRr v | throwError "z = A₁"
  let some v3 := find fun v => actR aRr (actR Z v) != v | throwError "A₁ z = 1"
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `PT) natT (lit PT)
    addDef (P ++ `SV) natT (lit (pack 24 SV))
    addDef (P ++ `SG) natT (lit (pack 12 rk))
    addDef (P ++ `ST) natT (lit (pack 12 order))
    addTree (P ++ `T) Ts
    addTree (P ++ `P) Ps
    addTree (P ++ `PI) PIs
    addTree (P ++ `SW) (sw.map (pack 11))
    addTree (P ++ `SK) (sw.map (·.size / 2))
    addDef (P ++ `PXY) natT (lit (pack 11 (comp n perms[10]! perms[11]!)))
    addDef (P ++ `TZ) natT (lit (packM (trR Z)))
    addTree (P ++ `V) #[v0, v1, v2, v3]

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kc_slices " pre:ident fId:ident ns:num : command => do
  let fN ← liftCoreM <| realizeGlobalConstNoOverload fId
  let P := pre.getId
  let NS := ns.getNat
  let FP := mkLambda `s .default natT (isTrue (mkApp (mkConst fN) (mkBVar 0)))
  liftCoreM <| withOptions (Elab.async.set · false) do
    for s in [0:NS] do
      let tyS := isTrue (mkApp (mkConst fN) (lit s))
      let nmS := P ++ Name.mkSimple s!"s{s}"
      CFSG.KC.addThmDecl <| { name := nmS, levelParams := [], type := tyS, value := reflBoolTrue }
    let ty := mkForall `s .default natT (mkForall `h .default
      (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit NS])
      (isTrue (mkApp (mkConst fN) (mkBVar 1))))
    let pf := forallChain FP NS fun s => mkConst (P ++ Name.mkSimple s!"s{s}")
    CFSG.KC.addThmDecl <| { name := P ++ `all, levelParams := [], type := ty, value := pf }

end

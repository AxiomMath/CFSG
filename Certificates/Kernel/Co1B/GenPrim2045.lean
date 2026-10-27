module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.ONSchreier.Native in
elab "#kss_co1prim " pre:ident sId:ident tId:ident rId:ident mId:ident : command => do
  let get := fun (i : Ident) => liftCoreM <| realizeGlobalConstNoOverload i
  let S ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) (← get sId)
  let T ← liftTermElabM <| unsafe evalConst (List CLevel) (← get tId)
  let R ← liftTermElabM <| unsafe evalConst (List Nat) (← get rId)
  let ms ← liftTermElabM <| unsafe evalConst
    (Nat → Array (Array Nat) → Nat → Nat → List (Nat × Nat × Nat)) (← get mId)
  let P := pre.getId
  let n := 1365
  let w := 11
  let G := S.extract 0 2
  let St := 32
  let mut lps : Array Nat := #[]
  let mut cnts : Array Nat := #[]
  let mut tps : Array Nat := #[]
  let mut pps : Array Nat := #[]
  let mut cks : Array (Array Nat) := #[]
  for x in R do
    let L := (ms n G 0 x).toArray
    let Lc := L.size
    let NS := (Lc + St - 1) / St
    lps := lps.push (pack w (L.foldl (fun a r => ((a.push r.1).push r.2.1).push r.2.2) #[]))
    cnts := cnts.push Lc
    let mut lab := Array.ofFn (n := n) fun i => if i.val = x then 0 else i.val
    let mut tp := Array.replicate n Lc
    let mut pp := Array.replicate n 0
    let mut ck : Array Nat := #[]
    for k in [0:Lc] do
      if k % St == 0 then ck := ck.push (pack w lab)
      let (i, u, v) := L[k]!
      let lp := lab[G[i]![u]!]!
      let lq := lab[G[i]![v]!]!
      if lq != lp then
        tp := tp.set! lq k
        pp := pp.set! lq lp
        lab := lab.map fun z => if z == lq then lp else z
    while ck.size ≤ NS do
      ck := ck.push (pack w lab)
    cks := cks.push ck
    tps := tps.push (pack 12 tp)
    pps := pps.push (pack w pp)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `LP) lps
    addTree (P ++ `CNT) cnts
    addTree (P ++ `TP) tps
    addTree (P ++ `PP) pps
    for l in [0:cks.size] do
      addTree (P ++ Name.mkSimple s!"A{l}") cks[l]!
    let Ta := T.toArray
    addTree (P ++ `M) (Ta.map (·.pts.size))
    addTree (P ++ `PTS) (Ta.map fun L => pack w L.pts)
    addTree (P ++ `POS) (Ta.map fun L => pack w L.pos)
    addTree (P ++ `PAR) (Ta.map fun L => pack w L.par)
    addTree (P ++ `LAB) (Ta.map fun L => pack w L.lab)

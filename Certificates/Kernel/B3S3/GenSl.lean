module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.BfsPinSlice
public import Certificates.Data.Kernel.Misc.ArrEnum
public import CFSG.Certificates.Kernel.Spor.RawDefs
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.LocalComp.BfsGen
public meta import Certificates.Kernel.B3S3.Gen
public meta import Lean
public import Certificates.Kernel.B3S3.Gen
public import Lean.Exception

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KC.B3S3Gen in
elab "#kb3_enum_sl " pre:ident gId:ident bId:ident nn:num ww:num ll:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let L := ll.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let gens ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let base ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  let (pts, edges) := CFSG.KC.BfsGen.search n w gens
  let N := pts.size
  if L == 0 || N % L != 0 then throwError "#kb3_enum_sl: {N} points, not a multiple of {L}"
  let K := N / L
  let tv := pts.map (pack w)
  let ev := edges.map (pack 16)
  let order := (Array.range tv.size).qsort fun a b => tv[a]! < tv[b]!
  let keyOf := fun (a : Array Nat) => base.toList.foldr (fun p acc => a[p]! + n * acc) 0
  let kv := pts.map keyOf
  let korder := ((Array.range kv.size).qsort fun a b => kv[a]! < kv[b]!).toList
  let cnt := fun (p : Nat) => Id.run do
    let mut c := 1
    for i in [0:p] do
      for j in edges[i]! do
        if j + 1 > c then c := j + 1
    return c
  let cs := Array.ofFn (n := K + 1) fun s => cnt (L * s.val)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `G) (gens.map (pack w))
    addDef (P ++ `ng) natT (lit gens.size)
    addDef (P ++ `N) natT (lit N)
    addTree (P ++ `T) tv
    addTree (P ++ `E) ev
    addTree (P ++ `S) order
    addTree (P ++ `C) cs
    addDef (P ++ `SK) listT (listE korder)
    let c := fun (s : Name) => mkConst (P ++ s)
    let nE := lit n
    let wE := lit w
    let refl : Name → Expr → CoreM Unit := fun nm ty => do
      CFSG.KC.addThmDecl
        { name := P ++ nm, levelParams := [], type := isTrue ty, value := reflBoolTrue }
    let mE := mkApp (mkConst ``CFSG.KS.mask) wE
    let nwE := mkApp2 (mkConst ``Nat.mul) nE wE
    let canonF := mkLambda `k .default natT (mkAppN (mkConst ``CFSG.KS.Prim.canonK)
      #[nE, wE, mE, nwE, mkApp (c `G) (mkBVar 0)])
    refl `g (mkApp2 (mkConst ``CFSG.KC.Enum.allN) (c `ng) canonF)
    refl `dist (mkAppN (mkConst ``CFSG.KC.BfsPin.distinctK) #[c `N, c `T, c `S])
    refl `t0 (mkApp2 (mkConst ``Nat.beq) (mkApp (c `T) (lit 0))
      (mkApp2 (mkConst ``CFSG.KC.Enum.pidn) nE wE))
    refl `c0 (mkApp2 (mkConst ``Nat.beq) (mkApp (c `C) (lit 0)) (lit 1))
    refl `cK (mkApp2 (mkConst ``Nat.beq) (mkApp (c `C) (lit K)) (c `N))
    let psE := mkApp2 (mkConst ``Array.toList [0]) natT (mkConst bN)
    refl `keys (mkAppN (mkConst ``CFSG.KC.BfsPin.keysSK) #[nE, wE, psE, c `N, c `T, c `SK])
    let csF := fun (sE : Expr) => mkAppN (mkConst ``CFSG.KC.BfsPin.canonSl) #[nE, wE, c `T, lit L, sE]
    let rsF := fun (sE : Expr) => mkAppN (mkConst ``CFSG.KC.BfsPin.runSl)
      #[nE, wE, c `ng, c `G, c `T, c `E, lit L, c `C, sE]
    for s in [0:K] do
      refl (Name.mkSimple s!"cs{s}") (csF (lit s))
      refl (Name.mkSimple s!"rs{s}") (rsF (lit s))
    let join : Name → String → (Expr → Expr) → CoreM Unit := fun nm pre F => do
      let body := mkLambda `s .default natT (isTrue (F (mkBVar 0)))
      let ty := mkForall `s .default natT (mkForall `h .default
        (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit K])
        (isTrue (F (mkBVar 1))))
      let v := forallChain body K fun s => mkConst (P ++ Name.mkSimple s!"{pre}{s}")
      CFSG.KC.addThmDecl <| { name := P ++ nm, levelParams := [], type := ty, value := v }
    join `csAll "cs" csF
    join `rsAll "rs" rsF
    addDef (P ++ `K) natT (lit K)
    addDef (P ++ `L) natT (lit L)

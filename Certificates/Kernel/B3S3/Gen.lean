module

public import Certificates.Kernel.LocalComp.BfsGen
public import Certificates.Data.Kernel.BfsPinBase
public import Certificates.Data.Kernel.Misc.ArrEnum
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.LocalComp.BfsGen
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KC.B3S3Gen

open CFSG.KC.Tab CFSG.KS.RawGen

meta def listE (l : List Nat) : Expr :=
  l.foldr (fun k acc => mkApp3 (mkConst ``List.cons [0]) natT (lit k) acc)
    (mkApp (mkConst ``List.nil [0]) natT)

meta def listT : Expr := mkApp (mkConst ``List [0]) natT

meta def idA (n : Nat) : Array Nat := Array.range n

meta def powA (n : Nat) (t : Array Nat) (e : Nat) : Array Nat := Id.run do
  let mut r := idA n
  for _ in [0:e] do
    r := comp n t r
  return r

meta def convWit (n : Nat) (pts : Array (Array Nat)) (qs rs : List Nat) :
    List Nat × List Nat := Id.run do
  let id := idA n
  let mut wj : Array Nat := #[]
  let mut wr : Array Nat := #[]
  for x in pts do
    let need := qs.any (fun q => powA n x q == id) && x != id
    let mut found : Option (Nat × Nat) := none
    if need then
      for j in [0:pts.size] do
        if found.isNone then
          let u := pts[j]!
          let z := comp n x (comp n u (comp n x (inv n u)))
          for r in rs do
            if found.isNone then
              let zr := powA n z r
              if zr != id && powA n zr 3 == id then
                found := some (j, r)
    let (a, b) := found.getD (0, 0)
    wj := wj.push a
    wr := wr.push b
  return (wj.toList, wr.toList)

end CFSG.KC.B3S3Gen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KC.B3S3Gen in
elab "#kb3_enum " pre:ident gId:ident bId:ident nn:num ww:num : command => do
  let P := pre.getId
  let n := nn.getNat
  let w := ww.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let gens ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) gN
  let base ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  let (pts, edges) := CFSG.KC.BfsGen.search n w gens
  let tv := pts.map (pack w)
  let ev := edges.map (pack 16)
  let order := (Array.range tv.size).qsort fun a b => tv[a]! < tv[b]!
  let keyOf := fun (a : Array Nat) => base.toList.foldr (fun p acc => a[p]! + n * acc) 0
  let kv := pts.map keyOf
  let korder := ((Array.range kv.size).qsort fun a b => kv[a]! < kv[b]!).toList
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `G) (gens.map (pack w))
    addDef (P ++ `ng) natT (lit gens.size)
    addDef (P ++ `N) natT (lit tv.size)
    addTree (P ++ `T) tv
    addTree (P ++ `E) ev
    addTree (P ++ `S) order
    addDef (P ++ `SK) listT (listE korder)
    let okT := isTrue (mkAppN (mkConst ``CFSG.KC.BfsPin.bfsK)
      #[lit n, lit w, mkConst (P ++ `ng), mkConst (P ++ `G), mkConst (P ++ `N), mkConst (P ++ `T),
        mkConst (P ++ `E), mkConst (P ++ `S)])
    CFSG.KC.addThmDecl <| { name := P ++ `ok, levelParams := [], type := okT, value := reflBoolTrue }
    let psE := mkApp2 (mkConst ``Array.toList [0]) natT (mkConst bN)
    let keysT := isTrue (mkAppN (mkConst ``CFSG.KC.BfsPin.keysSK)
      #[lit n, lit w, psE, mkConst (P ++ `N), mkConst (P ++ `T), mkConst (P ++ `SK)])
    let nK := P ++ `keys
    CFSG.KC.addThmDecl <| { name := nK, levelParams := [], type := keysT, value := reflBoolTrue }
    let permF := mkLambda `i .default natT (mkAppN (mkConst ``CFSG.KC.Misc.ArrEnum.permB)
      #[lit n, lit w, mkApp (mkConst (P ++ `T)) (mkBVar 0)])
    let permT := isTrue (mkApp2 (mkConst ``CFSG.KC.Enum.allN) (mkConst (P ++ `N)) permF)
    let nP := P ++ `perm
    CFSG.KC.addThmDecl <| { name := nP, levelParams := [], type := permT, value := reflBoolTrue }

end

module

public import Certificates.Kernel.B3S3.Gen
public meta import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KC.B3S3Gen in
elab "#kb3_enum_l " pre:ident gId:ident bId:ident nn:num ww:num : command => do
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

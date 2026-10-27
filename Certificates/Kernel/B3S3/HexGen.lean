module

public import Certificates.Data.Kernel.HexArrs
public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

open Lean Elab Command

open CFSG.KC.Tab in
elab "#kb3_hexarrs " pre:ident sId:ident dd:num nn:num ww:num : command => do
  let P := pre.getId
  let d := dd.getNat
  let n := nn.getNat
  let w := ww.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  let cs := s.toList.toArray
  if cs.size % (d * n) != 0 then throwError "#kb3_hexarrs: {cs.size} characters"
  let N := cs.size / (d * n)
  let hv := fun (c : Char) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 87
  let vals := Array.ofFn (n := N) fun j => Id.run do
    let mut acc := 0
    for i in [0:n] do
      let v := (List.range d).foldl (fun a t => a * 16 + hv cs[d * (n * j.val + i) + t]!) 0
      acc := acc ||| (v <<< (w * i))
    return acc
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KS.RawGen.addTree (P ++ `F) vals
    addDef (P ++ `N) natT (lit N)
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkAppN (mkConst ``CFSG.KC.HexArrs.hexArrsK)
        #[mkConst (P ++ `chars), lit d, lit n, lit w, mkConst (P ++ `N), mkConst (P ++ `F)])
      (mkConst ``Bool.true)
    let nAll := P ++ `all
    CFSG.KC.addThmDecl <| { name := nAll, levelParams := [], type := ty, value := reflBoolTrue }

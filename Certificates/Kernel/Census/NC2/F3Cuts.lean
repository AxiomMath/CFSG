module

public meta import Lean
public meta import Certificates.Kernel.LocalQT.Cmd
public meta import Certificates.Kernel.LocalComp.LayF3Cuts
public meta import Certificates.Kernel.LocalComp.ExprRead
public import Certificates.Data.Kernel.NC2L
public import Certificates.Data.Kernel.OpsLayF3
public import Certificates.Kernel.LocalQT.Cmd

open Lean Elab Command Meta CFSG.KC.LQT.Cmd CFSG.SectionRank.Native

public section

namespace CFSG.KC.LayF3CutsLive

elab "#lay_f3_cuts_live " pre:ident p:num d:num _K:num regs:ident ch:ident
    "[" cuts:num,* "]" : command => do
  let pre := pre.getId
  let c := layOf p.getNat d.getNat
  let S ← liftCoreM <| CFSG.KC.LayF3Cuts.natsOf (← liftCoreM <| realizeGlobalConstNoOverload regs)
  let chN ← liftCoreM <| realizeGlobalConstNoOverload ch
  let (n, ops) ← liftTermElabM do
    let C := mkConst chN
    let n ← CFSG.KC.ExprRead.natW (← mkAppM ``CFSG.KC.NC2L.LiveChunk.n #[C])
    let ops ← CFSG.KC.ExprRead.progW (← mkAppM ``CFSG.KC.NC2L.LiveChunk.prog #[C])
    return (n, ops)
  let R0 := (S ++ List.replicate (n - S.length) c.ONE).toArray
  withSync <| CFSG.KC.LayF3Cuts.cutsCore pre c R0 ops (cuts.getElems.toList.map (·.getNat))

end CFSG.KC.LayF3CutsLive

end

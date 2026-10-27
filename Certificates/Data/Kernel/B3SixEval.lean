module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.Kernel.B3SixK
public import CFSG.Assembly.Defs
public import CFSG.Certificates.Kernel.Common.Eval

namespace CFSG.KC.B3Six.Ev

open CFSG.KC.Eval CFSG.Quasithin.B3 CFSG.KC.B3Six

meta def tabsV (l : List (List Nat)) : Val :=
  .list (l.map fun t => .list (t.map Val.nat).toArray).toArray

public meta def four (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let some (Val.nat k) := args[0]? | throw "four: expected k"
  let some (Val.nat b) := args[1]? | throw "four: expected b"
  let m := if k = 0 then Mod.u0 else Mod.ut0
  let d := fourDX (permsK (List.range 6)) m (b == 1)
  return #[(`T, tabsV d.T), (`H1, tabsV d.H1), (`H2, tabsV d.H2), (`R1, tabsV d.R1),
    (`R2, tabsV d.R2), (`L1, tabsV d.L1), (`L2T, tabsV d.L2T), (`L1d, tabsV d.L1d),
    (`A1p, tabsV d.A1p), (`w, .nat d.w)]

end CFSG.KC.B3Six.Ev

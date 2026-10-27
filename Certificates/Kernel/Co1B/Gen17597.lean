module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.Co1B.Gen17590
public meta import Certificates.Data.TabMThreeALeech
public import Certificates.Kernel.Co1B.Gen17590

namespace CertificateChecks.KernelCo1B.Fix17597

open CFSG.KC.Eval CertificateChecks.KernelCo1B.Fix17590
  CFSG.HardMathSupport.Dickson.I271.TabMThreeALeech

public meta def rowsSel (s : Nat) : Array Nat :=
  match s with
  | 0 => c0Rows ()
  | 1 => CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native.rootRows 0
  | 2 => CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native.rootRows 2
  | _ => threeARows ()

public meta def fixStep17597 (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 1 then throw "fixStep17597: expected one argument"
  let s ← natV args[0]!
  let C := rowsSel s
  if C.size != 24 then throw "fixStep17597: expected 24 rows"
  let mut piv : Array (Nat × Nat × Nat) := #[]
  let mut ker : Array (Nat × Nat × Nat) := #[]
  for k in [0:24] do
    let e := 1 <<< k
    let (z, y) := reduceP piv (actRw C e ^^^ e) e
    if z != 0 then
      piv := piv.push (lowBit z, z, y)
    else
      let (f, _) := reduceP ker y 0
      ker := ker.push (lowBit f, f, 0)
  if piv.size + ker.size != 24 then throw "fixStep17597: wrong dimensions"
  let M := (List.range 24).foldl (fun acc i => acc ||| (C[i]! <<< (24 * i))) 0
  return #[(`M, .nat M), (`F, .list (ker.map fun p => .nat p.2.1)),
    (`Y, .list (piv.map fun p => .nat p.2.2))]

end CertificateChecks.KernelCo1B.Fix17597

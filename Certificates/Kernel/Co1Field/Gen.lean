module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public import CFSG.Certificates.Kernel.Common.Eval

namespace CertificateChecks.KernelCo1Field

open CFSG.KC.Eval

public meta def natsV (v : Val) : Except String (Array Nat) :=
  match v with
  | .list xs => xs.mapM fun x => match x with
    | .nat n => .ok n
    | _ => .error "expected a list of natural numbers"
  | _ => .error "expected a list"

public meta def colsM (g : Array Nat) : Array Nat :=
  Array.ofFn (n := 24) fun l => (List.range 24).foldl
    (fun acc q => if (g.getD q 0).testBit l.val then acc ||| (1 <<< q) else acc) 0

public meta def spreadM (x : Nat) : Nat :=
  (List.range 24).foldl (fun acc p => if x.testBit p then acc ||| (1 <<< (24 * p)) else acc) 0

public meta def commStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 3 then throw "commStep: expected g0 g1 free"
  let g0 ← natsV args[0]!
  let g1 ← natsV args[1]!
  let free ← natsV args[2]!
  let c0 := colsM g0
  let c1 := colsM g1
  let el := (List.range 1152).toArray.map fun c =>
    let (g, cc) := if c / 576 % 2 == 0 then (g0, c0) else (g1, c1)
    ((cc.getD (c % 24) 0) <<< (24 * (c / 24 % 24))) ^^^
      (spreadM (g.getD (c / 24 % 24) 0) <<< (c % 24))
  let nf := (List.range 576).foldl (fun acc v => if free.contains v then acc else acc ||| (1 <<< v)) 0
  return #[(`C0, .list (c0.map .nat)), (`C1, .list (c1.map .nat)), (`EL, .list (el.map .nat)),
    (`NF, .nat nf)]

end CertificateChecks.KernelCo1Field

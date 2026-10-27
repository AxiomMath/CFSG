module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.Sporadic.Co1I301.Inputs
public import CFSG.Assembly.Defs

namespace CertificateChecks.KernelCo1I301

open CFSG.KC.Eval CFSG.Sporadic.Co1I301.Native CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.Co1Patterson.Native

meta def packI (X : Array Nat) : Nat :=
  (List.range 24).foldl (fun acc i => acc ||| ((X.getD i 0 % 2 ^ 24) <<< (24 * i))) 0

meta def natsVI (xs : List Nat) : Val := .list (xs.toArray.map .nat)

public meta def step810305 (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "step810305: expected no arguments"
  let D := cDag ()
  if !D.2.2 then throw "step810305: inverse checks"
  let d := dRw ()
  let T := conjTree brayArr brayInvArr d 8960
  if T.1.size != 8960 then throw "step810305: orbit size"
  return #[(`CDS, natsVI (D.1.map packI)), (`CDIS, natsVI (D.2.1.map packI)),
    (`DSI, .nat (packI (inv (CFSG.HardMathSupport.Dickson.I271.TabMFive.subOneRows d)))),
    (`RP, natsVI (T.1.toList.drop 1)), (`RL, natsVI (T.2.toList.drop 1))]

end CertificateChecks.KernelCo1I301

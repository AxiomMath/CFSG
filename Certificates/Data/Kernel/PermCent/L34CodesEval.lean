module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public meta import CFSG.GH74.KGroups.L34AutInputs
public meta import CFSG.GH74.Uniqueness.SU.KI1r4F61L34MInputs
public import CFSG.Certificates.Kernel.Common.Eval

namespace CFSG.Certificates.Kernel.PkCV.L34Ev

open CFSG.KC.Eval CFSG.Certificates.Kernel.PkEnum CFSG.GH74.KGroups.L34
  CFSG.GH74.Uniqueness.SU.K.R4.L34M

meta def codeVP (a : VP 42) : Nat :=
  (List.range 42).foldr (fun i acc => acc ||| (CFSG.KS.PK.fd (wd 42) a.1.1 i <<< (6 * i))) 0

public meta def levQA (_ : Array Val) : Except String (Array (Lean.Name × Val)) :=
  let L := (List.finRange QA.baseCount).map fun i =>
    (transV (levelV (strongV QA) QA.base i)).map codeVP
  return #[(`lev, .list (L.map fun T => .list (T.map Val.nat).toArray).toArray)]

public meta def cl3A : Array (Array Nat) :=
  (cl3.map fun σ => (Array.ofFn fun i : Fin 42 => (σ i).val)).toArray

end CFSG.Certificates.Kernel.PkCV.L34Ev

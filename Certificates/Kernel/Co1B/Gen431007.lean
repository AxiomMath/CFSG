module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.Co1FiveRank
public import CFSG.Assembly.Defs

namespace CertificateChecks.KernelCo1B.Bound431007

open CFSG.KC.Eval CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative
  CFSG.LocalAnalysis.GLTheoremA.H1017.Co1FiveNative

public meta def kDag5 : List Rows × List Rows × Bool := kDag ext5

meta def encL5 (l : Int) : Nat := if 0 < l then 2 * l.toNat else 2 * (-l).toNat + 1

meta def natsV5 (xs : List Nat) : Val := .list (xs.toArray.map .nat)

meta def packF (X : Array Nat) : Nat :=
  (List.range 24).foldl (fun acc i => acc ||| ((X.getD i 0 % 2 ^ 24) <<< (24 * i))) 0

meta partial def greedySelF (pass : Array (Array Bool)) (cnt : Nat) (alive sel : Array Nat) :
    Except String (Array Nat) := do
  if alive.size ≤ cnt then return sel
  let mut best : Option (Nat × Nat) := none
  for j in [0:pass.size] do
    if !sel.contains j then
      let n := (alive.filter fun k => (pass[j]!)[k]!).size
      match best with
      | some (_, m) => if n < m then best := some (j, n)
      | none => best := some (j, n)
  match best with
  | some (j, n) =>
    if n == alive.size then throw "greedySelF: no condition removes a vector"
    greedySelF pass cnt (alive.filter fun k => (pass[j]!)[k]!) (sel.push j)
  | none => throw "greedySelF: conditions exhausted above the count"

meta def boundValsF (xs : Std.HashSet Nat) (cs : Array (Array Nat)) (base : List Nat)
    (conds : List (List Cond)) (cnts : List Nat) (sfx : String) :
    Except String (Array (Lean.Name × Val)) := do
  if certVecs.size != 9 * 13 * 840 then throw "boundValsF: |X| ≠ 98280"
  let mut SL : Array Val := #[]
  let mut CF : Array Val := #[]
  let mut CN : Array Val := #[]
  let mut NP : Array Val := #[]
  for i in [0:base.length] do
    let b := base.take i
    let u := base.getD i 0
    let cl := (conds.getD i []).toArray
    let pass := cl.map fun c =>
      let fv := fN cs b c.2
      let tu := typN xs (combN cs c.1 fv u)
      certVecs.map fun x => typN xs (combN cs c.1 fv x) == tu
    let sel ← greedySelF pass (cnts.getD i 0) (Array.range certVecs.size) #[]
    SL := SL.push (.list (sel.map .nat))
    CF := CF.push (.list (sel.map fun j =>
      let c := cl[j]!
      let fv := fN cs b c.2
      .list (((typN xs (combN cs c.1 fv u)) :: fv :: c.1).toArray.map .nat)))
    let ok := fun k => sel.all fun j => (pass[j]!)[k]!
    CN := CN.push (.list ((Array.range 9).map fun blk =>
      .nat ((Array.range (13 * 840)).filter fun k => ok (13 * 840 * blk + k)).size))
    let mut alive := Array.range certVecs.size
    let mut np := 0
    for j in sel do
      if np == 0 || alive.size ≥ 2000 then
        np := np + 1
        alive := alive.filter fun k => (pass[j]!)[k]!
    NP := NP.push (.nat np)
  return #[(Lean.Name.mkSimple ("T" ++ sfx), .list (cs.map fun c => .nat (packF c))),
    (Lean.Name.mkSimple ("Sel" ++ sfx), .list SL),
    (Lean.Name.mkSimple ("CFs" ++ sfx), .list CF),
    (Lean.Name.mkSimple ("CNs" ++ sfx), .list CN),
    (Lean.Name.mkSimple ("NP" ++ sfx), .list NP)]

public meta def stepF (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "stepF: expected no arguments"
  let D := kDag ext5
  if !D.2.2 then throw "stepF: inverse checks"
  let kR := nd D 88
  let cR := nd D 92
  let dR := nd D 94
  let xs := xsSet ()
  let words := chainDerivs () ++ ext5
  return #[(`KW, .list (words.toArray.map fun w => natsV5 (w.map encL5)))] ++
    (← boundValsF xs (colsOf (betas kR dR)) baseA condsA cntsA "A") ++
    (← boundValsF xs (colsOf (betas kR cR)) baseB condsB cntsB "B")

end CertificateChecks.KernelCo1B.Bound431007

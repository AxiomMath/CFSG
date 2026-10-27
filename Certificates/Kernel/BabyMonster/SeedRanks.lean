module

public import Certificates.Kernel.BabyMonster.Seeds
public import Certificates.Kernel.BabyMonster.ChainN
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.All
public import CFSG.Certificates.Kernel.Common.RankCert
public meta import Lean
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check4

public section

namespace CertificateChecks.KernelBM.SeedRanks

open CFSG.KC.BM CFSG.KC.BM.Fix CFSG.KC.BM.SL CFSG.KC.BSeed

inductive AllStripsP3 (Q : List Nat) : List Nat → List Nat → Prop
  | nil : AllStripsP3 Q [] []
  | cons (a c : Nat) (as cs : List Nat) :
      Nat.beq (Nat.xor (Nat.xor a (mulS Q a)) (mulS Q (mulS Q a))) c = true →
        AllStripsP3 Q as cs → AllStripsP3 Q (a :: as) (c :: cs)

open Lean Elab Tactic Meta in
elab "bm_strips3 " p:ident n:num : tactic => withMainContext do
  let P := p.getId
  let n := n.getNat
  if n == 0 then throwError "bm_strips3: no checks"
  let mut parts : Array (Expr × Expr × Expr) := #[]
  for i in [0:n] do
    let b ← checkLhsOf (P.appendAfter s!"{i}")
    let args := b.getAppArgs
    unless b.isAppOfArity ``Nat.beq 2 && args[0]!.isAppOfArity ``Nat.xor 2 &&
        args[0]!.appFn!.appArg!.isAppOfArity ``Nat.xor 2 &&
        args[0]!.appFn!.appArg!.appArg!.isAppOfArity ``CFSG.KC.BM.mulS 2 do
      throwError "bm_strips3: {P}{i} is not a check of `P (1 + Q + Q²) = R`"
    let y := args[0]!.appFn!.appArg!
    let m := y.appArg!
    parts := parts.push (m.appFn!.appArg!, y.appFn!.appArg!, args[1]!)
  let Q := parts[0]!.1
  let natE := mkConst ``Nat
  let mut acc := mkApp (mkConst ``AllStripsP3.nil) Q
  let mut as := mkApp (mkConst ``List.nil [0]) natE
  let mut cs := mkApp (mkConst ``List.nil [0]) natE
  for i' in [0:n] do
    let i := n - 1 - i'
    let (_, a, c) := parts[i]!
    acc := mkAppN (mkConst ``AllStripsP3.cons)
      #[Q, a, c, as, cs, mkConst (P.appendAfter s!"{i}"), acc]
    as := mkApp3 (mkConst ``List.cons [0]) natE a as
    cs := mkApp3 (mkConst ``List.cons [0]) natE c cs
  (← getMainGoal).assign acc
  replaceMainGoal []

local notation "sm" => stripMat

end CertificateChecks.KernelBM.SeedRanks

end

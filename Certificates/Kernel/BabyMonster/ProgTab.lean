module

public import CFSG.Certificates.Kernel.BabyMonster.ProgRun
public meta import Lean

public section

namespace CertificateChecks.KernelBM

open Lean Elab Tactic Meta

meta partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``List.cons 3 then
    return #[e.getArg! 1] ++ (← listElems (e.getArg! 2))
  if e.isAppOfArity ``List.nil 1 then
    return #[]
  if let some n := e.constName? then
    let some v := (← getConstInfo n).value? (allowOpaque := true)
      | throwError "bm_prog_cert: {n} has no value"
    return ← listElems v
  let e' ← whnfR e
  if e' != e then return ← listElems e'
  throwError "bm_prog_cert: not a list literal{indentExpr e}"

meta def natOf (e : Expr) : MetaM Nat := do
  if let some n := e.nat? then return n
  if let some n := e.rawNatLit? then return n
  let e' ← reduce e
  if let some n := e'.nat? then return n
  if let some n := e'.rawNatLit? then return n
  throwError "bm_prog_cert: not a numeral{indentExpr e}"

meta def dropLast (s : String) (k : Nat) : String := String.ofList (s.toList.take (s.length - k))

meta def prodFamilies (P : Name) : MetaM (Std.HashMap (Name × Name) (Name × Name)) := do
  let env ← getEnv
  let cands := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    match n with
    | .str pre s =>
      if pre == P && s.toList.take 2 == ['c', '_'] && s.toList.reverse.take 2 == ['0', '_'] then
        acc.push n
      else acc
    | _ => acc
  let mut m : Std.HashMap (Name × Name) (Name × Name) := {}
  for n in cands do
    let some ci := env.find? n | continue
    let some (_, b, _) := ci.type.eq? | continue
    unless b.isAppOfArity ``Nat.beq 2 do continue
    let lhs := b.getArg! 0
    let rhs := b.getArg! 1
    unless lhs.isAppOfArity ``CFSG.KC.BM.mulW 2 do continue
    let ws ← listElems (lhs.getArg! 0)
    unless ws.size == 1 do continue
    let some yN := ws[0]!.constName? | continue
    let some aN := (lhs.getArg! 1).constName? | continue
    let rhs ← if rhs.isAppOfArity ``CFSG.KC.BM.mulW 2 then do
        unless (← listElems (rhs.getArg! 0)).isEmpty do continue
        pure (rhs.getArg! 1)
      else pure rhs
    let some cN := rhs.constName? | continue
    let .str _ s := n | continue
    m := m.insert (aN.getPrefix, yN) (cN.getPrefix, .str P (dropLast s 2))
  return m

meta def familyStrips (F : Name) : MetaM Expr := do
  let natE := mkConst ``Nat
  let mut parts : Array (Expr × Expr × Expr) := #[]
  for i in [0:69] do
    let ci ← getConstInfo (F.appendAfter s!"_{i}")
    let some (_, b, _) := ci.type.eq? | throwError "bm_prog_cert: {F}_{i} is not a check"
    let args := b.getAppArgs
    parts := parts.push (args[0]!.appFn!.appArg!, args[0]!.appArg!, args[1]!)
  let Ws := parts[0]!.1
  let mut acc := mkApp (mkConst ``CFSG.KC.BM.AllStrips.nil) Ws
  let mut as := mkApp (mkConst ``List.nil [0]) natE
  let mut cs := mkApp (mkConst ``List.nil [0]) natE
  for i' in [0:69] do
    let i := 68 - i'
    let (_, a, c) := parts[i]!
    acc := mkAppN (mkConst ``CFSG.KC.BM.AllStrips.cons)
      #[Ws, a, c, as, cs, mkConst (F.appendAfter s!"_{i}"), acc]
    as := mkApp3 (mkConst ``List.cons [0]) natE a as
    cs := mkApp3 (mkConst ``List.cons [0]) natE c cs
  return acc

structure ProgSt where
  lits : Array Name := #[]
  index : Std.HashMap Name Nat := {}
  memo : Std.HashMap (Nat × Nat) Nat := {}
  tab : Array (Nat × Nat × Nat) := #[]
  fams : Array Name := #[]

meta def symMulN (fam : Std.HashMap (Name × Name) (Name × Name)) (x y : Option Nat) :
    StateT ProgSt MetaM (Option Nat) := do
  match x, y with
  | none, b => return b
  | some a, none => return some a
  | some a, some b =>
    let st ← get
    if let some z := st.memo[(a, b)]? then return some z
    let some (zN, F) := fam[(st.lits[a]!, st.lits[b]!)]?
      | throwError "bm_prog_cert: no product check for {st.lits[a]!} · {st.lits[b]!}"
    if st.index.contains zN then throwError "bm_prog_cert: {zN} is defined twice"
    let z := st.lits.size
    let st' : ProgSt :=
      { lits := st.lits.push zN
        index := st.index.insert zN z
        memo := st.memo.insert (a, b) z
        tab := st.tab.push (a, b, z)
        fams := st.fams.push F }
    set st'
    return some z

meta partial def symPowN (fam : Std.HashMap (Name × Name) (Name × Name)) (e : Nat) (x : Option Nat) :
    StateT ProgSt MetaM (Option Nat) := do
  if e == 0 then return none
  if e == 1 then return x
  let sq ← symMulN fam x x
  let y ← symPowN fam (e / 2) sq
  if e % 2 == 1 then symMulN fam x y else return y

meta def natE : Expr := mkConst ``Nat

meta def listE (ty : Expr) (es : List Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) ty e acc) (mkApp (mkConst ``List.nil [0]) ty)

meta def optNatE : Option Nat → Expr
  | none => mkApp (mkConst ``Option.none [0]) natE
  | some i => mkApp2 (mkConst ``Option.some [0]) natE (mkRawNatLit i)

meta def triE (x y z : Nat) : Expr :=
  let pE := mkApp2 (mkConst ``Prod [0, 0]) natE natE
  mkApp4 (mkConst ``Prod.mk [0, 0]) natE pE (mkRawNatLit x)
    (mkApp4 (mkConst ``Prod.mk [0, 0]) natE natE (mkRawNatLit y) (mkRawNatLit z))

meta def boolTrueRefl : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

elab "bm_prog_cert " p:ident h0:term:max h1:term:max : tactic => withMainContext do
  let P := p.getId
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let (prog, aN, bN, regs, tgt) ← forallTelescopeReducing ty fun xs body => do
    unless xs.size == 2 do throwError "bm_prog_cert: expected `∀ k < tgt.length, …`"
    let some (lhs, _) := body.and? | throwError "bm_prog_cert: expected a conjunction"
    let some (_, l, r) := lhs.eq? | throwError "bm_prog_cert: expected an equation"
    unless l.isAppOfArity ``CFSG.KC.BM.B9201.runM 6 do
      throwError "bm_prog_cert: expected `runM prog (stripMat A) (stripMat B) (regs k)`"
    let args := l.getAppArgs
    let some aN := args[3]!.appArg!.constName? | throwError "bm_prog_cert: `A` is not a constant"
    let some bN := args[4]!.appArg!.constName? | throwError "bm_prog_cert: `B` is not a constant"
    let regs := (← mkLambdaFVars #[xs[0]!] args[5]!).eta
    let tgt := r.appArg!.getArg! 1
    return (args[2]!, aN, bN, regs, tgt)
  let fam ← prodFamilies P
  let ins ← listElems prog
  let tgts ← (← listElems tgt).mapM fun e => do
    let some n := e.constName? | throwError "bm_prog_cert: a target is not a constant"
    return n
  let st0 : ProgSt := { lits := #[aN, bN], index := ({} : Std.HashMap Name Nat).insert aN 0 |>.insert bN 1 }
  let run : StateT ProgSt MetaM (Array (Option Nat) × Std.HashMap Nat (Option Nat)) := do
    let mut R : Std.HashMap Nat (Option Nat) := ({} : Std.HashMap Nat (Option Nat)).insert 1 (some 0)
      |>.insert 2 (some 1)
    let mut outs : Array (Option Nat) := #[]
    for e in ins do
      let fn := e.getAppFn.constName!
      let args ← e.getAppArgs.mapM fun a => (natOf a : MetaM Nat)
      let get (i : Nat) : Option Nat := (R[i]?).getD none
      let (v, k) ← if fn == ``CFSG.Monster.B.Primes.Native.Ins.mu then
          pure (← symMulN fam (get args[0]!) (get args[1]!), args[2]!)
        else if fn == ``CFSG.Monster.B.Primes.Native.Ins.pwr then
          pure (← symPowN fam args[0]! (get args[1]!), args[2]!)
        else throwError "bm_prog_cert: unsupported instruction{indentExpr e}"
      outs := outs.push v
      R := R.insert k v
    return (outs, R)
  let ((outs, R), st) ← run.run st0
  let mut idx : Array Nat := #[]
  for k in [0:tgts.size] do
    let r ← natOf (← whnf (mkApp regs (mkRawNatLit k)))
    let some (some i) := R[r]? | throwError "bm_prog_cert: register {r} holds no literal"
    unless st.lits[i]! == tgts[k]! do
      throwError "bm_prog_cert: register {r} holds {st.lits[i]!}, expected {tgts[k]!}"
    idx := idx.push i
  let listNatE := mkApp (mkConst ``List [0]) natE
  let LE := listE listNatE (st.lits.toList.map mkConst)
  let triT := mkApp2 (mkConst ``Prod [0, 0]) natE (mkApp2 (mkConst ``Prod [0, 0]) natE natE)
  let outsE := listE (mkApp (mkConst ``Option [0]) natE) (outs.toList.map optNatE)
  let idxE := listE natE (idx.toList.map mkRawNatLit)
  let mut htab := mkConst ``True.intro
  let mut suffix := mkApp (mkConst ``List.nil [0]) triT
  for k' in [0:st.tab.size] do
    let k := st.tab.size - 1 - k'
    let (x, y, z) := st.tab[k]!
    let pr ← familyStrips st.fams[k]!
    let tyK := mkApp3 (mkConst ``CFSG.KC.BM.AllStrips)
      (listE listNatE [mkConst st.lits[y]!]) (mkConst st.lits[x]!) (mkConst st.lits[z]!)
    let rest := mkApp2 (mkConst ``CFSG.KC.BM.Run.TabOK) LE suffix
    htab := mkApp4 (mkConst ``And.intro) tyK rest pr htab
    suffix := mkApp3 (mkConst ``List.cons [0]) triT (triE x y z) suffix
  let tabE := suffix
  let h0E ← Term.elabTerm h0 none
  let h1E ← Term.elabTerm h1 none
  let tgtT := mkApp (mkConst ``List [0]) listNatE
  let hL := mkApp2 (mkConst ``Eq.refl [1]) tgtT tgt
  let pf := mkAppN (mkConst ``CFSG.KC.BM.Run.progCert)
    #[LE, tabE, prog, outsE, regs, tgt, idxE, h0E, h1E, boolTrueRefl, htab, boolTrueRefl,
      boolTrueRefl, hL]
  goal.assign pf
  replaceMainGoal []

end CertificateChecks.KernelBM

end

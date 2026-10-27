module

public import CFSG.Certificates.Kernel.BabyMonster.RegRun
public import CFSG.Certificates.Kernel.BabyMonster.FourSound
public meta import Lean
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Monster.B.Max2.Pinned
public import CFSG.Monster.B.Pinned.GeneratorDeterminants
public import CFSG.Open.Defs
public import Certificates.Certificate3101
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3109Base
public import Certificates.Data.CFSGNative.MonsterB.DyadicFile

public section

namespace CertificateChecks.KernelBM.Reg

open Lean Elab Tactic Meta

meta partial def elems (e : Expr) : MetaM (Array Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``List.cons 3 then
    return #[e.getArg! 1] ++ (← elems (e.getArg! 2))
  if e.isAppOfArity ``List.nil 1 then
    return #[]
  if let some n := e.constName? then
    let some v := (← getConstInfo n).value? (allowOpaque := true)
      | throwError "bm_reg_cert: {n} has no value"
    return ← elems v
  let e' ← whnf e
  if e' != e then return ← elems e'
  throwError "bm_reg_cert: not a list literal{indentExpr e}"

meta def natV (e : Expr) : MetaM Nat := do
  if let some n := e.nat? then return n
  if let some n := e.rawNatLit? then return n
  let e' ← reduce e
  if let some n := e'.nat? then return n
  if let some n := e'.rawNatLit? then return n
  throwError "bm_reg_cert: not a numeral{indentExpr e}"

structure CE where
  a : Name
  ws : Array Name
  c : Name
  ds : Array Name
  fam : Name
  four : Bool
  wsE : Expr
  dsE : Expr

meta instance : Inhabited CE := ⟨⟨.anonymous, #[], .anonymous, #[], .anonymous, false, default, default⟩⟩

meta def litOf (e : Expr) : Option Name :=
  if e.isAppOfArity `CFSG.KC.BM.idS 1 then some `I
  else e.constName?.map Name.getPrefix

meta def names (e : Expr) : MetaM (Option (Array Name)) := do
  let xs ← elems e
  let ns := xs.filterMap Expr.constName?
  return if ns.size == xs.size then some ns else none

meta def families (Ps : Array Name) : MetaM (Array CE) := do
  let env ← getEnv
  let cands := env.constants.fold (init := (#[] : Array (Name × Bool))) fun acc n _ =>
    match n with
    | .str pre s =>
      if Ps.contains pre then
        if s.endsWith "_g0" then acc.push (n, true)
        else if s.endsWith "_0" then acc.push (n, false) else acc
      else acc
    | _ => acc
  let cands := cands.qsort fun x y => Name.quickLt x.1 y.1
  let mut out : Array CE := #[]
  for (n, four) in cands do
    let some ci := env.find? n | continue
    let some (_, b, _) := ci.type.eq? | continue
    let .str pre s := n | continue
    let fam := Name.str pre (String.ofList (s.toList.take (s.length - (if four then 3 else 2))))
    if four then
      unless b.isAppOfArity ``CFSG.KC.BM.mulW4 6 do continue
      let k := b.getArg! 5
      unless k.isAppOfArity ``CFSG.KC.BM.rhs4 5 do continue
      let some a := litOf (b.getArg! 1) | continue
      let some c := litOf (k.getArg! 1) | continue
      let some ws ← names (b.getArg! 0) | continue
      let some ds ← names (k.getArg! 0) | continue
      if a == `I then continue
      out := out.push { a, ws, c, ds, fam, four, wsE := b.getArg! 0, dsE := k.getArg! 0 }
    else
      unless b.isAppOfArity ``Nat.beq 2 do continue
      let l := b.getArg! 0
      let r := b.getArg! 1
      unless l.isAppOfArity ``CFSG.KC.BM.mulW 2 && r.isAppOfArity ``CFSG.KC.BM.mulW 2 do continue
      let some a := litOf (l.getArg! 1) | continue
      let some c := litOf (r.getArg! 1) | continue
      let some ws ← names (l.getArg! 0) | continue
      let some ds ← names (r.getArg! 0) | continue
      if a == `I then continue
      out := out.push { a, ws, c, ds, fam, four, wsE := l.getArg! 0, dsE := r.getArg! 0 }
  return out

meta def natE : Expr := mkConst ``Nat
meta def listNatE : Expr := mkApp (mkConst ``List [0]) natE

meta def listE (ty : Expr) (es : List Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) ty e acc) (mkApp (mkConst ``List.nil [0]) ty)

meta def natsE (l : List Nat) : Expr := listE natE (l.map mkRawNatLit)

meta def optE : Option Nat → Expr
  | none => mkApp (mkConst ``Option.none [0]) natE
  | some i => mkApp2 (mkConst ``Option.some [0]) natE (mkRawNatLit i)

meta def pairE (α β a b : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [0, 0]) α β a b

meta def prodT (α β : Expr) : Expr := mkApp2 (mkConst ``Prod [0, 0]) α β

meta def boolRefl : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

meta def familyStrips (e : CE) : MetaM (Expr × Expr) := do
  let mut parts : Array (Expr × Expr × Expr) := #[]
  for j in [0:69] do
    if e.four then
      let g := j / 4
      let i := j % 4
      let thm := e.fam.appendAfter s!"_g{g}"
      let ci ← getConstInfo thm
      let some (_, b, _) := ci.type.eq? | throwError "bm_reg_cert: {thm} is not a check"
      let args := b.getAppArgs
      let k := args[5]!
      let as := (Array.range 4).map fun t => args[1 + t]!
      let cs := (Array.range 4).map fun t => k.getArg! (1 + t)
      let pf := mkAppN (mkConst (`CFSG.KC.BM.F4 ++ Name.mkSimple s!"mulW4_sound{i}"))
        (#[e.wsE, e.dsE] ++ as ++ cs ++ #[mkConst thm])
      parts := parts.push (as[i]!, mkApp2 (mkConst ``CFSG.KC.BM.mulW) e.dsE cs[i]!, pf)
    else
      let thm := e.fam.appendAfter s!"_{j}"
      let ci ← getConstInfo thm
      let some (_, b, _) := ci.type.eq? | throwError "bm_reg_cert: {thm} is not a check"
      parts := parts.push ((b.getArg! 0).getArg! 1, b.getArg! 1, mkConst thm)
  let mut acc := mkApp (mkConst ``CFSG.KC.BM.AllStrips.nil) e.wsE
  let mut as := mkApp (mkConst ``List.nil [0]) natE
  let mut cs := mkApp (mkConst ``List.nil [0]) natE
  for j' in [0:69] do
    let (a, c, pf) := parts[68 - j']!
    acc := mkAppN (mkConst ``CFSG.KC.BM.AllStrips.cons) #[e.wsE, a, c, as, cs, pf, acc]
    as := mkApp3 (mkConst ``List.cons [0]) natE a as
    cs := mkApp3 (mkConst ``List.cons [0]) natE c cs
  return (acc, mkApp3 (mkConst ``CFSG.KC.BM.AllStrips) e.wsE as cs)

abbrev Rules := Std.HashMap (Name × Name) (Option Name)

meta partial def push (rs : Rules) (used : IO.Ref (Std.HashSet (Name × Name))) (x : Name) :
    List Name → IO (List Name)
  | [] => return [x]
  | y :: t => do
    match rs[(x, y)]? with
    | none => return x :: y :: t
    | some none => used.modify (·.insert (x, y)); return t
    | some (some z) => used.modify (·.insert (x, y)); push rs used z t

meta def red (rs : Rules) (used : IO.Ref (Std.HashSet (Name × Name))) (w : List Name) :
    IO (List Name) :=
  w.foldrM (fun x acc => push rs used x acc) []

structure St where
  defs : Std.HashMap Name CE
  rs : Rules
  atoms : Std.HashSet Name
  flat : Std.HashMap Name (List Name) := {}

meta partial def flatOf (st : IO.Ref St) (used : IO.Ref (Std.HashSet (Name × Name))) (y : Name) :
    IO (List Name) := do
  let s ← st.get
  if let some f := s.flat[y]? then return f
  let f ← match s.defs[y]? with
    | some e =>
      if s.atoms.contains y then pure [y]
      else do
        let mut w : List Name := []
        for z in (#[e.a] ++ e.ws) do
          w := w ++ (← flatOf st used z)
        red s.rs used w
    | none => pure [y]
  st.modify fun s => { s with flat := s.flat.insert y f }
  return f

meta def flatW (st : IO.Ref St) (used : IO.Ref (Std.HashSet (Name × Name))) (w : List Name) :
    IO (List Name) := do
  let mut c : List Name := []
  for x in w do
    c := c ++ (← flatOf st used x)
  red (← st.get).rs used c

meta def expand (st : IO.Ref St) (used : IO.Ref (Std.HashSet (Name × Name))) (x : Name) :
    IO (List Name) := do
  match (← st.get).defs[x]? with
  | none => return [x]
  | some e => flatW st used (e.a :: e.ws.toList)

structure RunR where
  outs : Array (List Name × Name)
  regs : Std.HashMap Nat (List Name)
  letters : Std.HashSet Name

meta def runProg (defs : Std.HashMap Name CE) (rs : Rules) (inv : Std.HashMap Name Name)
    (lits : Array Name) (atoms : Std.HashSet Name) (prog : Array (Name × Array Nat))
    (σ0 : Std.HashMap Nat (List Name)) (dflt verify : Bool)
    (used : IO.Ref (Std.HashSet (Name × Name))) : MetaM RunR := do
  let st ← IO.mkRef ({ defs, rs, atoms } : St)
  let st' ← IO.mkRef ({ defs, rs, atoms } : St)
  let junk ← IO.mkRef ({} : Std.HashSet (Name × Name))
  let mut byExp : Std.HashMap (List Name) Name := {}
  for x in lits do
    let f ← expand st' junk x
    unless byExp.contains f do byExp := byExp.insert f x
  let eqW (raw o : List Name) : MetaM Bool := do
    let fr ← flatW st used raw
    if fr == (← flatW st used o) then return true
    match o with
    | [x] => return fr == (← expand st used x)
    | _ => return false
  let mut R := σ0
  let mut outs : Array (List Name × Name) := #[]
  let mut letters : Std.HashSet Name := {}
  for (fn, a) in prog do
    let get (r : Nat) : MetaM (List Name) := do
      match R[r]? with
      | some w => pure w
      | none => if dflt then pure [] else throwError "bm_reg_cert: register {r} is read unset"
    let (o, v, k) ← if fn == `mu then do
        let raw := (← get a[0]!) ++ (← get a[1]!)
        let o ← red rs used raw
        if verify && !(← eqW raw o) then throwError "bm_reg_cert: `mu` check fails at {a}"
        pure (o, `I, a[2]!)
      else if fn == `pwr then do
        let u ← get a[1]!
        let raw := (List.replicate a[0]! u).flatten
        let fr ← flatW st' junk raw
        let o ← match byExp[fr]? with
          | some x => pure [x]
          | none => red rs used raw
        if verify && !(← eqW raw o) then throwError "bm_reg_cert: `pwr` check fails at {a}"
        pure (o, `I, a[2]!)
      else do
        let u ← get a[0]!
        match u with
        | [] => pure ([], `I, a[1]!)
        | _ =>
          let x ← match u with
            | [x] => pure x
            | _ => do
              let fr ← flatW st' junk u
              let some x := byExp[fr]? | throwError "bm_reg_cert: `iv` of a word of no literal at {a}"
              pure x
          let some y := inv[x]? | throwError "bm_reg_cert: no inverse rule for {x}"
          used.modify (·.insert (x, y))
          if verify && !(u == [x] || (← flatW st used u) == (← expand st used x)) then
            throwError "bm_reg_cert: `iv` check fails at {a}"
          pure ([y], x, a[1]!)
    outs := outs.push (o, v)
    R := R.insert k o
    for x in o do letters := letters.insert x
  return { outs, regs := R, letters }

elab "bm_reg_cert " "[" ps:ident,* "]" : tactic => withMainContext do
  let Ps := ps.getElems.map (·.getId)
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  unless ty.isAppOfArity ``CFSG.KC.BM.Reg.RegsOK 5 do
    throwError "bm_reg_cert: expected `RegsOK prog init dflt regs tgt`"
  let gargs := ty.getAppArgs
  let progE := gargs[0]!
  let initE := gargs[1]!
  let dfltE := gargs[2]!
  let regsE := gargs[3]!
  let tgtE := gargs[4]!
  let prog ← (← elems progE).mapM fun e => do
    let some fn := e.getAppFn.constName? | throwError "bm_reg_cert: not an instruction{indentExpr e}"
    let args : Array Nat ← e.getAppArgs.mapM fun a => (natV a : MetaM Nat)
    let k := match fn with
      | ``CFSG.Monster.B.Primes.Native.Ins.mu => `mu
      | ``CFSG.Monster.B.Primes.Native.Ins.iv => `iv
      | _ => `pwr
    return (k, args)
  let init ← (← elems initE).mapM fun e => do
    let e ← whnfR e
    unless e.isAppOfArity ``Prod.mk 4 do throwError "bm_reg_cert: not a pair{indentExpr e}"
    let r ← natV (e.getArg! 2)
    let o ← whnfR (e.getArg! 3)
    if o.isAppOfArity ``Option.none 1 then return (r, (none : Option Name))
    unless o.isAppOfArity ``Option.some 2 do throwError "bm_reg_cert: not an option{indentExpr o}"
    let some n := (o.getArg! 1).constName? | throwError "bm_reg_cert: an initial literal is not a constant"
    return (r, some n)
  let dflt := (← whnf dfltE).isConstOf ``Bool.true
  let regs : Array Nat ← (← elems regsE).mapM fun e => (natV e : MetaM Nat)
  let tgts ← (← elems tgtE).mapM fun e => do
    let some n := e.constName? | throwError "bm_reg_cert: a target is not a constant"
    return n
  let fams ← families Ps
  let mut defs : Std.HashMap Name CE := {}
  let mut rs : Rules := {}
  let mut inv : Std.HashMap Name Name := {}
  let mut ruleEnt : Std.HashMap (Name × Name) CE := {}
  for e in fams do
    if e.c != `I && e.ds.isEmpty && !(e.a :: e.ws.toList).contains e.c && !defs.contains e.c then
      defs := defs.insert e.c e
    if e.c == `I && e.ds.isEmpty && e.ws.size == 1 then
      let (x, y) := (e.a, e.ws[0]!)
      for (p, q) in [(x, y), (y, x)] do
        unless rs.contains (p, q) do
          rs := rs.insert (p, q) none
          ruleEnt := ruleEnt.insert (p, q) e
        unless inv.contains p do inv := inv.insert p q
  let mut litSet : Std.HashSet Name := {}
  for e in fams do
    for x in [e.a, e.c] ++ e.ws.toList ++ e.ds.toList do
      unless x == `I do litSet := litSet.insert x
  for (_, o) in init do
    if let some n := o then litSet := litSet.insert n
  for t in tgts do litSet := litSet.insert t
  let lits := litSet.toArray.qsort Name.quickLt
  let mut σ0 : Std.HashMap Nat (List Name) := {}
  for (r, o) in init.reverse do
    σ0 := σ0.insert r (match o with | none => [] | some n => [n])
  let atoms0 : Std.HashSet Name := lits.foldl (fun s x => if defs.contains x then s else s.insert x) {}
  let used0 ← IO.mkRef ({} : Std.HashSet (Name × Name))
  let r1 ← runProg defs rs inv lits atoms0 prog σ0 dflt false used0
  let mut atoms := atoms0
  for x in r1.letters do atoms := atoms.insert x
  for (_, w) in σ0 do
    for x in w do atoms := atoms.insert x
  let usedA ← IO.mkRef ({} : Std.HashSet (Name × Name))
  let rA ← runProg defs rs inv lits atoms prog σ0 dflt false usedA
  let stA ← IO.mkRef ({ defs, rs, atoms } : St)
  for k in [0:regs.size] do
    if let some u := rA.regs[regs[k]!]? then
      discard <| flatW stA usedA u
      discard <| expand stA usedA tgts[k]!
  let mut rsU : Rules := {}
  for p in (← usedA.get) do rsU := rsU.insert p none
  let used ← IO.mkRef ({} : Std.HashSet (Name × Name))
  let r2 ← runProg defs rsU inv lits atoms prog σ0 dflt true used
  let st ← IO.mkRef ({ defs, rs := rsU, atoms } : St)
  for k in [0:regs.size] do
    let r := regs[k]!
    let some u := r2.regs[r]? | throwError "bm_reg_cert: register {r} is never set"
    unless u == [tgts[k]!] do
      unless (← flatW st used u) == (← expand st used tgts[k]!) do
        throwError "bm_reg_cert: register {r} does not hold {tgts[k]!}"
  let mut need : Std.HashSet Name := {}
  let mut todo : Array Name := tgts
  for (_, o) in init do
    if let some n := o then todo := todo.push n
  for (o, v) in r2.outs do
    todo := todo ++ o.toArray
    if v != `I then todo := todo.push v
  let usedRules := (← used.get).toArray.qsort fun a b =>
    Name.quickLt a.1 b.1 || (a.1 == b.1 && Name.quickLt a.2 b.2)
  for (x, y) in usedRules do
    todo := todo.push x |>.push y
    let e := ruleEnt[(x, y)]!
    todo := todo.push e.a |>.append e.ws
  while h : todo.size > 0 do
    let x := todo.back
    todo := todo.pop
    if need.contains x then continue
    need := need.insert x
    if let some e := defs[x]? then
      todo := todo.push e.a |>.append e.ws
  let mut order : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  let mut stack : Array (Name × Bool) := (need.toArray.qsort Name.quickLt).reverse.map (·, false)
  while h : stack.size > 0 do
    let (x, done) := stack.back
    stack := stack.pop
    if done then
      order := order.push x
      continue
    if seen.contains x then continue
    seen := seen.insert x
    stack := stack.push (x, true)
    if let some e := defs[x]? then
      for y in (#[e.a] ++ e.ws).reverse do
        unless seen.contains y do stack := stack.push (y, false)
  let mut idx : Std.HashMap Name Nat := {}
  for x in order do idx := idx.insert x idx.size
  let ix (x : Name) : Nat := idx[x]!
  let mut tab : Array CE := #[]
  let mut wl : Array Name := #[]
  for x in order do
    match defs[x]? with
    | some e => tab := tab.push e
    | none => wl := wl.push x
  let mut ruleFams : Std.HashSet Name := {}
  for (x, y) in usedRules do
    let e := ruleEnt[(x, y)]!
    unless ruleFams.contains e.fam do
      ruleFams := ruleFams.insert e.fam
      tab := tab.push e
  let entT := prodT natE (prodT listNatE (prodT (mkApp (mkConst ``Option [0]) natE) listNatE))
  let entE (e : CE) : Expr :=
    pairE natE (prodT listNatE (prodT (mkApp (mkConst ``Option [0]) natE) listNatE))
      (mkRawNatLit (ix e.a))
      (pairE listNatE (prodT (mkApp (mkConst ``Option [0]) natE) listNatE)
        (natsE (e.ws.toList.map ix))
        (pairE (mkApp (mkConst ``Option [0]) natE) listNatE
          (optE (if e.c == `I then none else some (ix e.c))) (natsE (e.ds.toList.map ix))))
  let LE := listE listNatE (order.toList.map mkConst)
  let tabE := listE entT (tab.toList.map entE)
  let mut htab := mkConst ``True.intro
  let mut suffix := mkApp (mkConst ``List.nil [0]) entT
  for k' in [0:tab.size] do
    let e := tab[tab.size - 1 - k']!
    let (pr, tyK) ← familyStrips e
    let rest := mkApp2 (mkConst ``CFSG.KC.BM.Reg.TabOK) LE suffix
    htab := mkApp4 (mkConst ``And.intro) tyK rest pr htab
    suffix := mkApp3 (mkConst ``List.cons [0]) entT (entE e) suffix
  let mut hwl := mkConst ``True.intro
  let mut wsuf := mkApp (mkConst ``List.nil [0]) natE
  for k' in [0:wl.size] do
    let x := wl[wl.size - 1 - k']!
    let .str pre s := x | throwError "bm_reg_cert: bad literal name {x}"
    let wn := Name.str pre ("wf_" ++ s)
    let some ci := (← getEnv).find? wn | throwError "bm_reg_cert: {x} has no definition and no {wn}"
    let rest := mkApp2 (mkConst ``CFSG.KC.BM.Reg.WfL) LE wsuf
    hwl := mkApp4 (mkConst ``And.intro) ci.type rest (mkConst wn) hwl
    wsuf := mkApp3 (mkConst ``List.cons [0]) natE (mkRawNatLit (ix x)) wsuf
  let ruleT := prodT natE (prodT natE (mkApp (mkConst ``Option [0]) natE))
  let rsE := listE ruleT (usedRules.toList.map fun (x, y) =>
    pairE natE (prodT natE (mkApp (mkConst ``Option [0]) natE)) (mkRawNatLit (ix x))
      (pairE natE (mkApp (mkConst ``Option [0]) natE) (mkRawNatLit (ix y)) (optE none)))
  let mut rsK : Rules := {}
  for (x, y) in usedRules do rsK := rsK.insert (x, y) none
  let stU ← IO.mkRef ({ defs, rs := rsK, atoms } : St)
  let dummy ← IO.mkRef ({} : Std.HashSet (Name × Name))
  let mut fls : Array Expr := #[]
  for x in order do
    let f ← if atoms.contains x || !defs.contains x then pure [x] else flatOf stU dummy x
    fls := fls.push (natsE (f.map ix))
  let FsE := listE listNatE fls.toList
  let SE := natsE (order.toList.filter (fun x => atoms.contains x || !defs.contains x) |>.map ix)
  let outT := prodT listNatE natE
  let outsE := listE outT (r2.outs.toList.map fun (o, v) =>
    pairE listNatE natE (natsE (o.map ix)) (mkRawNatLit (if v == `I then 0 else ix v)))
  let optT := mkApp (mkConst ``Option [0]) natE
  let initIE := listE (prodT natE optT) (init.toList.map fun (r, o) =>
    pairE natE optT (mkRawNatLit r) (optE (o.map ix)))
  let idxE := natsE (tgts.toList.map ix)
  let initT := prodT natE (mkApp (mkConst ``Option [0]) listNatE)
  let hinit := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``List [0]) initT) initE
  let hidx := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``List [0]) listNatE) tgtE
  let pf := mkAppN (mkConst ``CFSG.KC.BM.Reg.regCert)
    #[LE, tabE, natsE (wl.toList.map ix), rsE, FsE, SE, progE, outsE, initIE, dfltE, regsE, idxE,
      initE, tgtE, hwl, htab, boolRefl, boolRefl, boolRefl, boolRefl, boolRefl, hinit, hidx]
  goal.assign pf
  replaceMainGoal []

end CertificateChecks.KernelBM.Reg

end

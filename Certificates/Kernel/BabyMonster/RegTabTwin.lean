module

public import CFSG.Certificates.Kernel.BabyMonster.RegPow
public import CFSG.Certificates.Kernel.BabyMonster.FourSound
public meta import Certificates.Kernel.BabyMonster.RegTab
public import Certificates.Kernel.BabyMonster.RegTab

public section

namespace CertificateChecks.KernelBM.RegTwin

open Lean Elab Tactic Meta CertificateChecks.KernelBM.Reg

elab "bm_reg_cert_twin " "[" ps:ident,* "]" : tactic => withMainContext do
  let Ps := ps.getElems.map (·.getId)
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  unless ty.isAppOfArity ``CFSG.KC.BM.Reg.RegsOK 5 do
    throwError "bm_reg_cert_twin: expected `RegsOK prog init dflt regs tgt`"
  let gargs := ty.getAppArgs
  let progE := gargs[0]!
  let initE := gargs[1]!
  let dfltE := gargs[2]!
  let regsE := gargs[3]!
  let tgtE := gargs[4]!
  let prog ← (← elems progE).mapM fun e => do
    let some fn := e.getAppFn.constName? | throwError "bm_reg_cert_twin: not an instruction{indentExpr e}"
    let args : Array Nat ← e.getAppArgs.mapM fun a => (natV a : MetaM Nat)
    let k := match fn with
      | ``CFSG.Monster.B.Primes.Native.Ins.mu => `mu
      | ``CFSG.Monster.B.Primes.Native.Ins.iv => `iv
      | _ => `pwr
    return (k, args)
  let init ← (← elems initE).mapM fun e => do
    let e ← whnfR e
    unless e.isAppOfArity ``Prod.mk 4 do throwError "bm_reg_cert_twin: not a pair{indentExpr e}"
    let r ← natV (e.getArg! 2)
    let o ← whnfR (e.getArg! 3)
    if o.isAppOfArity ``Option.none 1 then return (r, (none : Option Name))
    unless o.isAppOfArity ``Option.some 2 do throwError "bm_reg_cert_twin: not an option{indentExpr o}"
    let some n := (o.getArg! 1).constName? | throwError "bm_reg_cert_twin: an initial literal is not a constant"
    return (r, some n)
  let dflt := (← whnf dfltE).isConstOf ``Bool.true
  let regs : Array Nat ← (← elems regsE).mapM fun e => (natV e : MetaM Nat)
  let tgts ← (← elems tgtE).mapM fun e => do
    let some n := e.constName? | throwError "bm_reg_cert_twin: a target is not a constant"
    return n
  let fams := (← families Ps).qsort fun x y => Name.cmp x.fam y.fam == .lt
  let mut cdefs : Std.HashMap Name (Array CE) := {}
  let mut rules : Rules := {}
  let mut ruleEnt : Std.HashMap (Name × Name) CE := {}
  let mut inv : Std.HashMap Name Name := {}
  for e in fams do
    if e.c != `I && e.ds.isEmpty && !(e.a :: e.ws.toList).contains e.c then
      cdefs := cdefs.insert e.c ((cdefs.getD e.c #[]).push e)
    if e.c == `I && e.ds.isEmpty && e.ws.size == 1 then
      for (p, q) in [(e.a, e.ws[0]!), (e.ws[0]!, e.a)] do
        unless rules.contains (p, q) do
          rules := rules.insert (p, q) none
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
  let mut pw : Std.HashMap Name (Name × Nat) := {}
  for x in lits do pw := pw.insert x (x, 1)
  let mut defs : Std.HashMap Name CE := {}
  for (x, es) in cdefs do defs := defs.insert x es[0]!
  let mut changed := true
  while changed do
    changed := false
    for x in lits do
      let self := pw[x]!.1 == x
      for e in cdefs.getD x #[] do
        unless self || e.fam == defs[x]!.fam do continue
        let ps := (#[e.a] ++ e.ws).map fun y => pw[y]!
        let b := ps[0]!.1
        if b != x && ps.all (·.1 == b) then
          let new := (b, ps.foldl (fun s p => s + p.2) 0)
          if pw[x]! != new then
            pw := pw.insert x new
            defs := defs.insert x e
            changed := true
          break
  let mut ords : Std.HashMap Name Nat := {}
  let mut ordEnt : Std.HashMap Name CE := {}
  for e in fams do
    if e.c == `I && e.ds.isEmpty then
      let ps := (#[e.a] ++ e.ws).map fun y => pw[y]!
      let b := ps[0]!.1
      if ps.all (·.1 == b) && !ords.contains b then
        ords := ords.insert b (ps.foldl (fun s p => s + p.2) 0)
        ordEnt := ordEnt.insert b e
  let mut use : Std.HashMap Name Nat := {}
  for (_, e) in defs do
    for y in #[e.a] ++ e.ws do use := use.insert y (use.getD y 0 + 1)
  let pref (a b : Name) : Bool := use.getD a 0 > use.getD b 0 ||
    (use.getD a 0 == use.getD b 0 && Name.quickLt a b)
  let mut byBase : Std.HashMap Name (Array (Name × Nat)) := {}
  for x in lits do
    let (b, k) := pw[x]!
    byBase := byBase.insert b ((byBase.getD b #[]).push (x, k))
  let mut powRule : Std.HashSet (Name × Name) := {}
  for (b, L) in byBase do
    if L.size < 2 then continue
    let n := ords.getD b 0
    let L := L.qsort fun p q => pref p.1 q.1
    for (x, i) in L do
      for (y, j) in L do
        if rules.contains (x, y) then continue
        let s := if n == 0 then i + j else (i + j) % n
        if n != 0 && s == 0 then
          rules := rules.insert (x, y) none
          powRule := powRule.insert (x, y)
          unless inv.contains x do inv := inv.insert x y
        else if let some (z, _) := L.find? fun (_, k) => (if n == 0 then k else k % n) == s then
          rules := rules.insert (x, y) (some z)
          powRule := powRule.insert (x, y)
  let used ← IO.mkRef ({} : Std.HashSet (Name × Name))
  let junk ← IO.mkRef ({} : Std.HashSet (Name × Name))
  let mut byDef : Std.HashMap (List Name) Name := {}
  let mut byDefAll : Std.HashMap (List Name) (Array Name) := {}
  let mut keyOf : Std.HashMap Name (List Name) := {}
  for x in lits do
    let some e := defs[x]? | continue
    let w ← red rules junk (e.a :: e.ws.toList)
    unless byDef.contains w do byDef := byDef.insert w x
    byDefAll := byDefAll.insert w ((byDefAll.getD w #[]).push x)
    keyOf := keyOf.insert x w
  let mut R : Std.HashMap Nat (List Name) := {}
  for (r, o) in init.reverse do
    R := R.insert r (match o with | none => [] | some n => [n])
  let mut last : Std.HashMap Nat Nat := {}
  let mut outs : Array (List Name × Name) := #[]
  for t in [0:prog.size] do
    let (fn, a) := prog[t]!
    let get (R : Std.HashMap Nat (List Name)) (r : Nat) : MetaM (List Name) := do
      match R[r]? with
      | some w => pure w
      | none => if dflt then pure [] else throwError "bm_reg_cert_twin: register {r} is read unset"
    let mat (R : Std.HashMap Nat (List Name)) (outs : Array (List Name × Name)) (r : Nat) :
        MetaM (Option Name × Std.HashMap Nat (List Name) × Array (List Name × Name)) := do
      let w ← get R r
      match w with
      | [] => return (none, R, outs)
      | [x] => return (some x, R, outs)
      | _ =>
        let k ← red rules junk w
        let some s := byDef[k]? |
          throwError "bm_reg_cert_twin: register {r} holds no literal at {a} (word {w}, reduced {k})"
        let some t' := last[r]? | throwError "bm_reg_cert_twin: register {r} is never written"
        return (some s, R.insert r [s], outs.set! t' ([s], outs[t']!.2))
    let twins (r : Nat) (s : Name) : Array Name :=
      match last[r]?, keyOf[s]? with
      | some w, some key =>
        if prog[w]!.1 == `mu && outs[w]!.2 == `I then byDefAll.getD key #[s]
        else if prog[w]!.1 == `pwr then
          match pw[s]? with
          | some (b, i0) =>
            let n := ords.getD b 0
            #[s] ++ ((byBase.getD b #[]).filter fun (p, k) =>
              p != s && (k == i0 || (n != 0 && k % n == i0 % n))).map (·.1)
          | none => #[s]
        else #[s]
      | _, _ => #[s]
    if fn == `mu then
      let (i, j, k) := (a[0]!, a[1]!, a[2]!)
      let mut vi : List Name := []
      let mut vj : List Name := []
      if i == k && j == k then
        let (s, R', outs') ← mat R outs k
        R := R'
        outs := outs'
        vi := s.toList
        vj := s.toList
      else
        if i == k then vi ← get R i
        else
          let (s, R', outs') ← mat R outs i
          R := R'
          outs := outs'
          vi := s.toList
        if j == k then vj ← get R j
        else
          let (s, R', outs') ← mat R outs j
          R := R'
          outs := outs'
          vj := s.toList
        if i != k && j != k then
          if let ([si], [sj]) := (vi, vj) then
            let k0 ← red rules junk [si, sj]
            unless byDef.contains k0 do
              let mut found : Option (Name × Name) := none
              for ti in twins i si do
                for tj in twins j sj do
                  if found.isNone && (i != j || ti == tj) then
                    if byDef.contains (← red rules junk [ti, tj]) then found := some (ti, tj)
              if let some (ti, tj) := found then
                for (r, x) in [(i, ti), (j, tj)] do
                  if let some w := last[r]? then
                    R := R.insert r [x]
                    outs := outs.set! w ([x], outs[w]!.2)
                vi := [ti]
                vj := [tj]
      outs := outs.push (vi ++ vj, `I)
      R := R.insert k (vi ++ vj)
      last := last.insert k t
    else if fn == `pwr then
      let (e, i, k) := (a[0]!, a[1]!, a[2]!)
      let (s, R', outs') ← mat R outs i
      R := R'
      outs := outs'
      let o ← match s with
        | none => pure ([], `I)
        | some s =>
          if e == 1 then pure ([s], `I)
          else
            let (b, i0) := pw[s]!
            let n := ords.getD b 0
            let cands := (byBase.getD b #[]).filter fun (_, k) =>
              k == i0 * e || (n != 0 && k % n == (i0 * e) % n)
            let cands := cands.qsort fun p q => pref p.1 q.1
            match cands[0]? with
            | some (p, _) => pure ([p], s)
            | none => throwError "bm_reg_cert_twin: no literal for {s} ^ {e} ({s} = {b} ^ {i0}, \
                powers of {b}: {(byBase.getD b #[]).toList})"
      outs := outs.push o
      R := R.insert k o.1
      last := last.insert k t
    else
      let (i, k) := (a[0]!, a[1]!)
      let (s, R', outs') ← mat R outs i
      R := R'
      outs := outs'
      let o ← match s with
        | none => pure ([], `I)
        | some s =>
          let some y := inv[s]? | throwError "bm_reg_cert_twin: no inverse rule for {s}"
          pure ([y], s)
      outs := outs.push o
      R := R.insert k o.1
      last := last.insert k t
  for k in [0:regs.size] do
    let r := regs[k]!
    let w ← match R[r]? with
      | some w => pure w
      | none => throwError "bm_reg_cert_twin: register {r} is never set"
    unless w == [tgts[k]!] do
      let kk ← red rules junk w
      unless byDef[kk]? == some tgts[k]! do
        throwError "bm_reg_cert_twin: register {r} does not hold {tgts[k]!}"
      let some t' := last[r]? | throwError "bm_reg_cert_twin: register {r} is never written"
      outs := outs.set! t' ([tgts[k]!], outs[t']!.2)
  let mut σ : Std.HashMap Nat (List Name) := {}
  for (r, o) in init.reverse do
    σ := σ.insert r (match o with | none => [] | some n => [n])
  let mut contracted : Std.HashSet Name := {}
  for t in [0:prog.size] do
    let (fn, a) := prog[t]!
    let (o, v) := outs[t]!
    let rd (r : Nat) : List Name := σ.getD r []
    let defW (x : Name) : List Name := match defs[x]? with
      | some e => e.a :: e.ws.toList
      | none => [x]
    let eqW (raw o : List Name) : MetaM Bool := do
      let r1 ← red rules used raw
      if r1 == (← red rules used o) then return true
      match o with
      | [x] =>
        if r1 == (← red rules used (defW x)) then return true
        return false
      | _ => return false
    let ok ← if fn == `mu then eqW (rd a[0]! ++ rd a[1]!) o
      else if fn == `pwr then do
        if v == `I then eqW (List.replicate a[0]! (rd a[1]!)).flatten o
        else pure (rd a[1]! == [v])
      else do
        match rd a[0]! with
        | [] => pure (o == [])
        | u =>
          used.modify (·.insert (v, o.head!))
          pure (u == [v])
    unless ok do throwError "bm_reg_cert_twin: the check of instruction {t} fails"
    if let [x] := o then
      if fn == `mu && defs.contains x then contracted := contracted.insert x
    σ := σ.insert (match fn with | `mu => a[2]! | `pwr => a[2]! | _ => a[1]!) o
  for k in [0:regs.size] do
    unless σ.getD regs[k]! [] == [tgts[k]!] do
      throwError "bm_reg_cert_twin: register {regs[k]!} does not end as {tgts[k]!}"
  let usedRules := (← used.get).toArray.qsort fun a b =>
    Name.quickLt a.1 b.1 || (a.1 == b.1 && Name.quickLt a.2 b.2)
  let mut pwNeed : Std.HashSet Name := {}
  let mut ordNeed : Std.HashSet Name := {}
  for (x, y) in usedRules do
    if powRule.contains (x, y) then
      pwNeed := pwNeed.insert x |>.insert y
      if let some (some z) := rules[(x, y)]? then pwNeed := pwNeed.insert z
      ordNeed := ordNeed.insert pw[x]!.1
  for t in [0:prog.size] do
    let (fn, a) := prog[t]!
    let (o, v) := outs[t]!
    if fn == `pwr && v != `I then
      pwNeed := pwNeed.insert v |>.insert o.head!
      ordNeed := ordNeed.insert pw[v]!.1
  let ordList := (ordNeed.toArray.qsort Name.quickLt).filter (ords.contains ·)
  for b in ordList do
    let e := ordEnt[b]!
    for y in #[e.a] ++ e.ws do pwNeed := pwNeed.insert y
  let mut pwList : Array Name := #[]
  let mut pwSeen : Std.HashSet Name := {}
  let mut stack : Array (Name × Bool) := (pwNeed.toArray.qsort Name.quickLt).map (·, false)
  while h : stack.size > 0 do
    let (x, done) := stack.back
    stack := stack.pop
    if done then
      pwList := pwList.push x
      continue
    if pwSeen.contains x then continue
    pwSeen := pwSeen.insert x
    stack := stack.push (x, true)
    if pw[x]!.1 != x then
      let e := defs[x]!
      for y in (#[e.a] ++ e.ws).reverse do
        unless pwSeen.contains y do stack := stack.push (y, false)
  let wfName (x : Name) : Option Name := match x with
    | .str pre s => some (Name.str pre ("wf_" ++ s))
    | _ => none
  let env ← getEnv
  let hasWf (x : Name) : Bool := match wfName x with
    | some n => env.contains n
    | none => false
  let mut defNeed : Std.HashSet Name := contracted
  for x in tgts do if defs.contains x then defNeed := defNeed.insert x
  for x in pwList do if pw[x]!.1 != x then defNeed := defNeed.insert x
  let mut extra : Array CE := #[]
  let mut extraF : Std.HashSet Name := {}
  for (x, y) in usedRules do
    unless powRule.contains (x, y) do
      let e := ruleEnt[(x, y)]!
      unless extraF.contains e.fam do
        extraF := extraF.insert e.fam
        extra := extra.push e
  for b in ordList do
    let e := ordEnt[b]!
    unless extraF.contains e.fam do
      extraF := extraF.insert e.fam
      extra := extra.push e
  let mut todo : Array Name := #[]
  for x in defNeed do
    let e := defs[x]!
    todo := todo.append (#[e.a] ++ e.ws)
  for e in extra do todo := todo.append (#[e.a] ++ e.ws)
  for (o, v) in outs do
    todo := todo.append o.toArray
    if v != `I then todo := todo.push v
  for (_, o) in init do if let some n := o then todo := todo.push n
  todo := todo.append tgts
  todo := todo.append pwList
  let mut need : Std.HashSet Name := {}
  while h : todo.size > 0 do
    let x := todo.back
    todo := todo.pop
    if need.contains x then continue
    need := need.insert x
    if defNeed.contains x then
      let e := defs[x]!
      todo := todo.append (#[e.a] ++ e.ws)
    else if !hasWf x then
      match defs[x]? with
      | some e =>
        defNeed := defNeed.insert x
        todo := todo.append (#[e.a] ++ e.ws)
      | none => throwError "bm_reg_cert_twin: {x} has no definition and no wf_ check"
  let mut order : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  let mut stk : Array (Name × Bool) := (need.toArray.qsort Name.quickLt).reverse.map (·, false)
  while h : stk.size > 0 do
    let (x, done) := stk.back
    stk := stk.pop
    if done then
      order := order.push x
      continue
    if seen.contains x then continue
    seen := seen.insert x
    stk := stk.push (x, true)
    if defNeed.contains x then
      let e := defs[x]!
      for y in (#[e.a] ++ e.ws).reverse do
        unless seen.contains y do stk := stk.push (y, false)
  let mut idx : Std.HashMap Name Nat := {}
  for x in order do idx := idx.insert x idx.size
  let ix (x : Name) : Nat := idx[x]!
  let mut tab : Array CE := #[]
  let mut wl : Array Name := #[]
  for x in order do
    if defNeed.contains x then tab := tab.push defs[x]!
    else wl := wl.push x
  tab := tab.append extra
  let optT := mkApp (mkConst ``Option [0]) natE
  let entT := prodT natE (prodT listNatE (prodT optT listNatE))
  let entE (e : CE) : Expr :=
    pairE natE (prodT listNatE (prodT optT listNatE)) (mkRawNatLit (ix e.a))
      (pairE listNatE (prodT optT listNatE) (natsE (e.ws.toList.map ix))
        (pairE optT listNatE (optE (if e.c == `I then none else some (ix e.c)))
          (natsE (e.ds.toList.map ix))))
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
    let some wn := wfName x | throwError "bm_reg_cert_twin: bad literal name {x}"
    let some ci := env.find? wn | throwError "bm_reg_cert_twin: {x} has no {wn}"
    let rest := mkApp2 (mkConst ``CFSG.KC.BM.Reg.WfL) LE wsuf
    hwl := mkApp4 (mkConst ``And.intro) ci.type rest (mkConst wn) hwl
    wsuf := mkApp3 (mkConst ``List.cons [0]) natE (mkRawNatLit (ix x)) wsuf
  let ruleT := prodT natE (prodT natE optT)
  let rsE := listE ruleT (usedRules.toList.map fun (x, y) =>
    pairE natE (prodT natE optT) (mkRawNatLit (ix x))
      (pairE natE optT (mkRawNatLit (ix y)) (optE ((rules[(x, y)]!).map ix))))
  let pwT := prodT natE (prodT natE natE)
  let PE := listE pwT (pwList.toList.map fun x =>
    let (b, k) := pw[x]!
    pairE natE (prodT natE natE) (mkRawNatLit (ix x))
      (pairE natE natE (mkRawNatLit (ix b)) (mkRawNatLit k)))
  let ordsE := listE (prodT natE natE) (ordList.toList.map fun b =>
    pairE natE natE (mkRawNatLit (ix b)) (mkRawNatLit (ords[b]!)))
  let FsE := listE listNatE (order.toList.map fun x => natsE [ix x])
  let SE := natsE (order.toList.map ix)
  let outsE := listE (prodT listNatE natE) (outs.toList.map fun (o, v) =>
    pairE listNatE natE (natsE (o.map ix)) (mkRawNatLit (if v == `I then 0 else ix v)))
  let initIE := listE (prodT natE optT) (init.toList.map fun (r, o) =>
    pairE natE optT (mkRawNatLit r) (optE (o.map ix)))
  let idxE := natsE (tgts.toList.map ix)
  let initT := prodT natE (mkApp (mkConst ``Option [0]) listNatE)
  let hinit := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``List [0]) initT) initE
  let hidx := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``List [0]) listNatE) tgtE
  let pf := mkAppN (mkConst ``CFSG.KC.BM.Reg.regCertM)
    #[LE, tabE, natsE (wl.toList.map ix), rsE, PE, ordsE, FsE, SE, progE, outsE, initIE, dfltE,
      regsE, idxE, initE, tgtE, hwl, htab, boolRefl, boolRefl, boolRefl, boolRefl, boolRefl,
      boolRefl, boolRefl, hinit, hidx]
  goal.assign pf
  replaceMainGoal []

end CertificateChecks.KernelBM.RegTwin

end

module

public import Certificates.Data.Kernel.Bounds.Table
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Data.Kernel.Bounds.Table

open Lean Elab Command

public section

namespace CFSG.Certificates.KB

theorem brec_false (x c : Bool) : Bool.rec false x c = (c && x) := by cases c <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem wordsOkB_succ (Wd R S : Nat → Nat) (inv eps nR nS n : Nat) :
    wordsOkB Wd R S inv eps nR nS (n + 1) = (wordOkB R S inv eps nR nS (Wd n) &&
      (lettersLe eps (Wd n) && wordsOkB Wd R S inv eps nR nS n)) := by
  rw [show wordsOkB Wd R S inv eps nR nS (n + 1) = Bool.rec false (Bool.rec false
    (wordsOkB Wd R S inv eps nR nS n) (lettersLe eps (Wd n))) (wordOkB R S inv eps nR nS (Wd n))
    from rfl, brec_false, brec_false]

theorem wordsOkB_add (Wd R S : Nat → Nat) (inv eps nR nS a : Nat) : ∀ b : Nat,
    wordsOkB Wd R S inv eps nR nS (a + b) =
      (wordsOkB Wd R S inv eps nR nS a && wordsOkB (fun i => Wd (i + a)) R S inv eps nR nS b)
  | 0 => by rw [Nat.add_zero, show wordsOkB (fun i => Wd (i + a)) R S inv eps nR nS 0 = true
      from rfl, Bool.and_true]
  | b + 1 => by
    rw [← Nat.add_assoc, wordsOkB_succ, wordsOkB_succ, wordsOkB_add Wd R S inv eps nR nS a b,
      Nat.add_comm b a]
    cases wordOkB R S inv eps nR nS (Wd (a + b)) <;> cases lettersLe eps (Wd (a + b)) <;>
      simp

theorem wordsOkB_step (Wd R S : Nat → Nat) (inv eps nR nS k0 a b : Nat)
    (h1 : wordsOkB (fun i => Wd (Nat.add i k0)) R S inv eps nR nS a = true)
    (h2 : wordsOkB (fun i => Wd (Nat.add i (Nat.add k0 a))) R S inv eps nR nS b = true) :
    wordsOkB (fun i => Wd (Nat.add i k0)) R S inv eps nR nS (Nat.add a b) = true := by
  have e : (fun i => (fun j => Wd (Nat.add j k0)) (i + a)) =
      fun i => Wd (Nat.add i (Nat.add k0 a)) := by
    funext i
    simp only [Nat.add_eq]
    congr 1
    omega
  rw [Nat.add_eq, wordsOkB_add, e, h1, h2, Bool.and_self]

theorem words2Ok_succ (Wd Wd2 : Nat → Nat) (inv n : Nat) :
    words2Ok Wd Wd2 inv (n + 1) = (Nat.beq (Wd2 n) (pairs inv (Wd n)) && words2Ok Wd Wd2 inv n) := by
  rw [show words2Ok Wd Wd2 inv (n + 1) = Bool.rec false (words2Ok Wd Wd2 inv n)
    (Nat.beq (Wd2 n) (pairs inv (Wd n))) from rfl, brec_false]

theorem words2Ok_add (Wd Wd2 : Nat → Nat) (inv a : Nat) : ∀ b : Nat,
    words2Ok Wd Wd2 inv (a + b) =
      (words2Ok Wd Wd2 inv a && words2Ok (fun i => Wd (i + a)) (fun i => Wd2 (i + a)) inv b)
  | 0 => by rw [Nat.add_zero, show words2Ok (fun i => Wd (i + a)) (fun i => Wd2 (i + a)) inv 0 =
      true from rfl, Bool.and_true]
  | b + 1 => by
    rw [← Nat.add_assoc, words2Ok_succ, words2Ok_succ, words2Ok_add Wd Wd2 inv a b,
      Nat.add_comm b a]
    cases Nat.beq (Wd2 (a + b)) (pairs inv (Wd (a + b))) <;> simp

theorem words2Ok_step (Wd Wd2 : Nat → Nat) (inv k0 a b : Nat)
    (h1 : words2Ok (fun i => Wd (Nat.add i k0)) (fun i => Wd2 (Nat.add i k0)) inv a = true)
    (h2 : words2Ok (fun i => Wd (Nat.add i (Nat.add k0 a)))
      (fun i => Wd2 (Nat.add i (Nat.add k0 a))) inv b = true) :
    words2Ok (fun i => Wd (Nat.add i k0)) (fun i => Wd2 (Nat.add i k0)) inv (Nat.add a b) =
      true := by
  have e : ∀ T : Nat → Nat, (fun i => (fun j => T (Nat.add j k0)) (i + a)) =
      fun i => T (Nat.add i (Nat.add k0 a)) := by
    intro T
    funext i
    simp only [Nat.add_eq]
    congr 1
    omega
  rw [Nat.add_eq, words2Ok_add, e Wd, e Wd2, h1, h2, Bool.and_self]

theorem treeRange_succ (F D : Nat → Nat) (L n k0 c : Nat) :
    treeRange F D L n k0 (c + 1) =
      (treeOk' D L n (Nat.add k0 (Nat.succ c)) (F (Nat.add k0 c)) && treeRange F D L n k0 c) := by
  rw [show treeRange F D L n k0 (c + 1) = andB (treeOk' D L n (Nat.add k0 (Nat.succ c))
    (F (Nat.add k0 c))) (treeRange F D L n k0 c) from rfl, andB_eq]

theorem treeRange_add (F D : Nat → Nat) (L n k0 a : Nat) : ∀ b : Nat,
    treeRange F D L n k0 (a + b) = (treeRange F D L n k0 a && treeRange F D L n (k0 + a) b)
  | 0 => by rw [Nat.add_zero, show treeRange F D L n (k0 + a) 0 = true from rfl, Bool.and_true]
  | b + 1 => by
    rw [← Nat.add_assoc, treeRange_succ, treeRange_succ, treeRange_add F D L n k0 a b]
    have e1 : Nat.add k0 (Nat.succ (a + b)) = Nat.add (k0 + a) (Nat.succ b) := by
      simp only [Nat.add_eq]
      omega
    have e2 : Nat.add k0 (a + b) = Nat.add (k0 + a) b := by
      simp only [Nat.add_eq]
      omega
    rw [e1, e2]
    cases treeOk' D L n (Nat.add (k0 + a) (Nat.succ b)) (F (Nat.add (k0 + a) b)) <;> simp

theorem treeRange_step (F D : Nat → Nat) (L n k0 a b : Nat) (h1 : treeRange F D L n k0 a = true)
    (h2 : treeRange F D L n (Nat.add k0 a) b = true) :
    treeRange F D L n k0 (Nat.add a b) = true := by
  rw [Nat.add_eq, treeRange_add, h1, ← Nat.add_eq, h2, Bool.and_self]

theorem wWalkList_append (F Wd2 : Nat → Nat) (RW RM nCos nW : Nat) :
    ∀ (l1 l2 : List Nat) (f : Nat), wWalkList F Wd2 RW RM nCos nW (List.append l1 l2) f =
      wWalkList F Wd2 RW RM nCos nW l2 (wWalkList F Wd2 RW RM nCos nW l1 f)
  | [], _, _ => rfl
  | E :: l1, l2, f => wWalkList_append F Wd2 RW RM nCos nW l1 l2 (wElem F Wd2 RW RM nCos nW E f)

theorem walk_step (F Wd2 : Nat → Nat) (RW RM nCos nW : Nat) (l1 l2 : List Nat) (x y z : Nat)
    (h1 : Nat.beq (wWalkList F Wd2 RW RM nCos nW l1 x) y = true)
    (h2 : Nat.beq (wWalkList F Wd2 RW RM nCos nW l2 y) z = true) :
    Nat.beq (wWalkList F Wd2 RW RM nCos nW (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [wWalkList_append, h1, h2]

theorem wCovList_append (F : Nat → Nat) (RW RM N L nF : Nat) :
    ∀ (l1 l2 : List Nat) (x : Nat), wCovList F RW RM N L nF (List.append l1 l2) x =
      wCovList F RW RM N L nF l2 (wCovList F RW RM N L nF l1 x)
  | [], _, _ => rfl
  | E :: l1, l2, x => wCovList_append F RW RM N L nF l1 l2 (wCovElem F RW RM N L nF E x)

theorem cov_step (F : Nat → Nat) (RW RM N L nF : Nat) (l1 l2 : List Nat) (x y z : Nat)
    (h1 : Nat.beq (wCovList F RW RM N L nF l1 x) y = true)
    (h2 : Nat.beq (wCovList F RW RM N L nF l2 y) z = true) :
    Nat.beq (wCovList F RW RM N L nF (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [wCovList_append, h1, h2]

theorem tableOk_intro (inv L eps nLab nT N RW RM nR nS nW nF : Nat) (F D Wd Wd2 R S : Nat → Nat)
    (amap : Nat) (rels words : List (List (Nat × Bool))) (walk cov : List Nat)
    (h1 : Nat.ble (Nat.succ L) (nat_lit 128) = true) (h2 : Nat.ble (nat_lit 1) N = true)
    (h3 : Nat.ble N nLab = true)
    (h4 : Nat.beq nLab (Nat.succ nT) = true) (h5 : Nat.ble (Nat.succ nLab) bad = true)
    (h6 : Nat.ble (Nat.succ nF) bad = true) (h6a : Nat.ble (Nat.succ nR) bad = true)
    (h6b : Nat.ble (Nat.succ nS) bad = true) (h6c : lensLt rels (nat_lit 256) = true)
    (h6d : lensLt words (nat_lit 256) = true) (h7 : hdrOk inv L eps amap = true)
    (h8 : relsOk R nR amap rels = true) (h9 : subsOk S nS amap words = true)
    (h10 : wordsOkB (fun i => Wd (Nat.add i (nat_lit 0))) R S inv eps nR nS nW = true)
    (h11 : words2Ok (fun i => Wd (Nat.add i (nat_lit 0))) (fun i => Wd2 (Nat.add i (nat_lit 0)))
      inv nW = true)
    (h12 : treeRange F D L nLab (nat_lit 0) nT = true)
    (h13 : Nat.beq (wWalkList F Wd2 RW RM nLab nW walk nT) nF = true)
    (h14 : Nat.beq (wCovList F RW RM N L nF cov (nat_lit 0)) N = true) :
    tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true := by
  have h10' : wordsOkB Wd R S inv eps nR nS nW = true := h10
  have h11' : words2Ok Wd Wd2 inv nW = true := h11
  simp only [tableOk, andB_eq, h1, h2, h3, h4, h5, h6, h6a, h6b, h6c, h6d, h7, h8, h9, h10', h11',
    h12, h13, h14, Bool.and_self]

end CFSG.Certificates.KB

namespace CFSG.Certificates.KB.Assemble

open CFSG.Certificates.KB.Checks CFSG.Certificates.KB.Cert

meta def kbc (s : String) : Name := `CFSG.Certificates.KB ++ s.toName

meta def sh (T : Expr) (k0 : Nat) : Expr := shifted T k0

meta partial def sliceTree (per n : Nat) (leaf : Nat → Expr)
    (node : Nat → Nat → Nat → Expr → Expr → Expr) (lo hi : Nat) : Expr × Nat × Nat :=
  if hi = lo + 1 then (leaf lo, per * lo, min per (n - per * lo))
  else
    let mid := lo + (hi - lo) / 2
    let (p1, k0, a) := sliceTree per n leaf node lo mid
    let (p2, _, b) := sliceTree per n leaf node mid hi
    (node k0 a b p1 p2, k0, a + b)

meta partial def listTree (D : Name) (pre : String) (pts : Array Nat) (leaf : Nat → Expr)
    (node : Expr → Expr → Nat → Nat → Nat → Expr → Expr → Expr) (lo hi : Nat) : Expr × Expr :=
  if hi = lo + 1 then (mkConst (elemName D pre lo), leaf lo)
  else
    let mid := lo + (hi - lo) / 2
    let (l1, p1) := listTree D pre pts leaf node lo mid
    let (l2, p2) := listTree D pre pts leaf node mid hi
    (mkApp3 (mkConst ``List.append [Level.zero]) natT l1 l2,
      node l1 l2 pts[lo]! pts[mid]! pts[hi]! p1 p2)

meta def isTrue (b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)

meta def proofOf (T P R : Name) (c : Counts) : Array (String × Expr × Expr) × ((String → Expr) → Expr) :=
  let D := `CFSG.KBData ++ P
  let d := fun (s : String) => mkConst (D ++ s.toName)
  let chk := fun (s : String) => mkConst (`CFSG.KBCheck3 ++ P ++ s.toName)
  let nWC := (c.nW + 999) / 1000
  let nTC := (c.nT + 299) / 300
  let words :=
    if nWC = 0 then reflBoolTrue
    else (sliceTree 1000 c.nW (fun k => chk s!"words{k}")
      (fun k0 a b p1 p2 => mkAppN (mkConst (kbc "wordsOkB_step"))
        #[d "Wd", d "R", d "S", lit c.inv, lit c.eps, lit c.nR, lit c.nS, lit k0, lit a, lit b,
          p1, p2]) 0 nWC).1
  let pairs :=
    if nWC = 0 then reflBoolTrue
    else (sliceTree 1000 c.nW (fun k => chk s!"pairs{k}")
      (fun k0 a b p1 p2 => mkAppN (mkConst (kbc "words2Ok_step"))
        #[d "Wd", d "Wd2", lit c.inv, lit k0, lit a, lit b, p1, p2]) 0 nWC).1
  let tree :=
    if nTC = 0 then reflBoolTrue
    else (sliceTree 300 c.nT (fun k => chk s!"tree{k}")
      (fun k0 a b p1 p2 => mkAppN (mkConst (kbc "treeRange_step"))
        #[d "F", d "D", lit c.L, lit c.nLab, lit k0, lit a, lit b, p1, p2]) 0 nTC).1
  let nWE := c.wf.size - 1
  let nilE := mkApp (mkConst ``List.nil [Level.zero]) natT
  let (walkL, walk) :=
    if nWE = 0 then (nilE, reflBoolTrue)
    else listTree D "wl" c.wf (fun j => chk s!"walk{j}")
      (fun l1 l2 x y z p1 p2 => mkAppN (mkConst (kbc "walk_step"))
        #[d "F", d "Wd2", lit c.RW, lit c.RM, lit c.nLab, lit c.nW, l1, l2, lit x, lit y, lit z,
          p1, p2]) 0 nWE
  let nCE := c.cx.size - 1
  let (covL, cov) :=
    if nCE = 0 then (nilE, reflBoolTrue)
    else listTree D "cv" c.cx (fun j => chk s!"cov{j}")
      (fun l1 l2 x y z p1 p2 => mkAppN (mkConst (kbc "cov_step"))
        #[d "F", lit c.RW, lit c.RM, lit c.N, lit c.L, lit c.nF, l1, l2, lit x, lit y, lit z,
          p1, p2]) 0 nCE
  let wordsT := isTrue (mkAppN (mkConst (kbc "wordsOkB"))
    #[sh (d "Wd") 0, d "R", d "S", lit c.inv, lit c.eps, lit c.nR, lit c.nS, lit c.nW])
  let pairsT := isTrue (mkAppN (mkConst (kbc "words2Ok"))
    #[sh (d "Wd") 0, sh (d "Wd2") 0, lit c.inv, lit c.nW])
  let treeT := isTrue (mkAppN (mkConst (kbc "treeRange"))
    #[d "F", d "D", lit c.L, lit c.nLab, lit 0, lit c.nT])
  let walkT := isTrue (mkApp2 (mkConst ``Nat.beq) (mkAppN (mkConst (kbc "wWalkList"))
    #[d "F", d "Wd2", lit c.RW, lit c.RM, lit c.nLab, lit c.nW, walkL, lit c.nT]) (lit c.nF))
  let covT := isTrue (mkApp2 (mkConst ``Nat.beq) (mkAppN (mkConst (kbc "wCovList"))
    #[d "F", lit c.RW, lit c.RM, lit c.N, lit c.L, lit c.nF, covL, lit 0]) (lit c.N))
  let parts := #[("words", wordsT, words), ("pairs", pairsT, pairs), ("tree", treeT, tree),
    ("walk", walkT, walk), ("cov", covT, cov)]
  (parts, fun part => mkAppN (mkConst (kbc "tableOk_intro"))
    #[lit c.inv, lit c.L, lit c.eps, lit c.nLab, lit c.nT, lit c.N, lit c.RW, lit c.RM, lit c.nR,
      lit c.nS, lit c.nW, lit c.nF, d "F", d "D", d "Wd", d "Wd2", d "R", d "S",
      mkConst (T ++ `amap), mkConst R, mkConst (T ++ `words), walkL, covL,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue,
      reflBoolTrue, reflBoolTrue, reflBoolTrue, reflBoolTrue, mkConst (T ++ `hdr_ok), mkConst (T ++ `rels_ok), mkConst (T ++ `subs_ok),
      part "words", part "pairs", part "tree", part "walk", part "cov"])

meta def litVal (what : String) (e : Expr) : MetaM Nat := do
  let .lit (.natVal n) := e | throwError "kb_assemble: {what} is not a raw literal: {e}"
  return n

meta def elemPoints (P : Name) (kind : String) (start : Nat) : MetaM (Array Nat) := do
  let env ← getEnv
  let mut pts := #[start]
  let mut j := 0
  repeat
    let some ci := env.find? (`CFSG.KBCheck3 ++ P ++ Name.mkSimple s!"{kind}{j}") | break
    let some (_, lhs, _) := ci.type.eq? | throwError "kb_assemble: {ci.name} is not an equation"
    let #[f, y] := lhs.getAppArgs | throwError "kb_assemble: {ci.name} is not a `Nat.beq`"
    unless (← litVal "start" f.appArg!) == pts.back! do
      throwError "kb_assemble: {ci.name} does not start where the previous {kind} check ends"
    pts := pts.push (← litVal "end" y)
    j := j + 1
  return pts

end CFSG.Certificates.KB.Assemble

open CFSG.Certificates.KB.Checks CFSG.Certificates.KB.Cert CFSG.Certificates.KB.Assemble in
elab "kb_assemble " p:ident : tactic =>
  Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
      | throwError "kb_assemble: the goal is not `T.ok = true`"
    let .const okN _ := lhs | throwError "kb_assemble: the goal is not `T.ok = true`"
    let some (.defnInfo d) := (← getEnv).find? okN
      | throwError "kb_assemble: {okN} is not a definition"
    let a := d.value.getAppArgs
    unless d.value.isAppOf (kb "tableOk").constName! && a.size == 23 do
      throwError "kb_assemble: {okN} is not a `tableOk` application"
    let v ← (a.extract 0 12).mapIdxM fun i e => litVal s!"argument {i} of tableOk" e
    let .const R _ := a[19]! | throwError "kb_assemble: the relators of {okN} are not a constant"
    let P := p.getId
    let c : Counts :=
      { inv := v[0]!, L := v[1]!, eps := v[2]!, nLab := v[3]!, nT := v[4]!, N := v[5]!,
        RW := v[6]!, RM := v[7]!, nR := v[8]!, nS := v[9]!, nW := v[10]!, nF := v[11]!,
        wf := ← elemPoints P "walk" v[4]!, cx := ← elemPoints P "cov" 0 }
    let (parts, pf) := proofOf okN.getPrefix P R c
    g.assign (pf fun s => (parts.find? (·.1 == s)).get!.2.2)

open CFSG.Certificates.KB.Checks CFSG.Certificates.KB.Cert CFSG.Certificates.KB.Assemble in
elab "#kb_assemble " ns:ident t:ident p:ident "include_bytes" path:str size:num hash:num
    rels:ident nm:ident : command => do
  let b ← CFSG.Certificates.KB.Load.readPinned path.getString size.getNat hash.getNat
  let c := counts (parseHeader b)
  let T := ns.getId ++ t.getId
  let (parts, pf) := proofOf T p.getId rels.getId c
  let N := nm.getId
  CFSG.Certificates.KB.Load.withSync do
    for (s, type, value) in parts do
      try CFSG.KC.addThmDecl <| { name := N ++ s.toName, levelParams := [], type, value }
      catch e => throwError "{N ++ s.toName}: {e.toMessageData}"
    CFSG.KC.addThmDecl <|
      { name := N, levelParams := [], type := isTrue (mkConst (T ++ `ok)),
        value := pf fun s => mkConst (N ++ s.toName) }

end

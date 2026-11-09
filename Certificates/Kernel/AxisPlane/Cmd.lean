module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Kernel.AxisPlane.Gen
public import Certificates.Data.Kernel.AxisPlane.Chk
public import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Kernel.AxisPlane.Gen

public section

namespace CertificateChecks.KernelAP

theorem forall_lt_zero' (P : Nat → Prop) : ∀ i, i < 0 → P i :=
  fun i h => absurd h (Nat.not_lt_zero i)

theorem forall_lt_succ' {P : Nat → Prop} {n : Nat} (h : ∀ i, i < n → P i) (hn : P n) :
    ∀ i, i < n + 1 → P i :=
  fun i hi => (Nat.lt_succ_iff_lt_or_eq.1 hi).elim (h i) (fun e => e ▸ hn)

theorem bandL (a b : Bool) (h : Bool.rec (motive := fun _ => Bool) false b a = true) : a = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · rfl

theorem bandR (a b : Bool) (h : Bool.rec (motive := fun _ => Bool) false b a = true) : b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact h

end CertificateChecks.KernelAP

namespace CFSG.KC.AxisPlane

@[expose] noncomputable def chunkPairK (w : Nat) (cs : List Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → Bool → List Nat)
    (fun p h => Bool.rec (motive := fun _ => List Nat) List.nil (List.cons p List.nil) h)
    (fun c _ ih p h => Bool.rec (motive := fun _ => List Nat) (ih c true)
      (List.cons (Nat.lor p (Nat.shiftLeft c w)) (ih (nat_lit 0) false)) h) cs (nat_lit 0) false

@[expose] noncomputable def chunkStripK (cs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun c _ ih => List.cons (Nat.shiftRight c (nat_lit 64)) ih) cs

@[expose] noncomputable def chunkJoinK (k w : Nat) (cs : List Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → Nat)
    (fun _ cs => List.rec (motive := fun _ => Nat) (nat_lit 0) (fun c _ _ => c) cs)
    (fun _ ih w cs => ih (Nat.add w w) (chunkPairK w cs)) k w cs

theorem chunkPairK_getD_go (w : Nat) : ∀ (cs : List Nat) (p j : Nat),
    (List.rec (motive := fun _ => Nat → Bool → List Nat)
      (fun p h => Bool.rec (motive := fun _ => List Nat) List.nil (List.cons p List.nil) h)
      (fun c _ ih p h => Bool.rec (motive := fun _ => List Nat) (ih c true)
        (List.cons (Nat.lor p (Nat.shiftLeft c w)) (ih (nat_lit 0) false)) h) cs p false).getD j 0 =
      (cs.getD (2 * j) 0 ||| cs.getD (2 * j + 1) 0 <<< w) ∧
    (List.rec (motive := fun _ => Nat → Bool → List Nat)
      (fun p h => Bool.rec (motive := fun _ => List Nat) List.nil (List.cons p List.nil) h)
      (fun c _ ih p h => Bool.rec (motive := fun _ => List Nat) (ih c true)
        (List.cons (Nat.lor p (Nat.shiftLeft c w)) (ih (nat_lit 0) false)) h) cs p true).getD j 0 =
      ((p :: cs).getD (2 * j) 0 ||| (p :: cs).getD (2 * j + 1) 0 <<< w)
  | [], p, j => by
    refine ⟨by simp, ?_⟩
    cases j <;> simp
  | c :: t, p, j => by
    refine ⟨(chunkPairK_getD_go w t c j).2, ?_⟩
    cases j with
    | zero => rfl
    | succ j =>
      have := (chunkPairK_getD_go w t 0 j).1
      simp only [List.getD_cons_succ] at this ⊢
      rw [Nat.mul_succ, List.getD_cons_succ, List.getD_cons_succ]
      exact this

theorem chunkPairK_getD (w : Nat) (cs : List Nat) (j : Nat) :
    (chunkPairK w cs).getD j 0 = (cs.getD (2 * j) 0 ||| cs.getD (2 * j + 1) 0 <<< w) :=
  (chunkPairK_getD_go w cs 0 j).1

theorem chunkPairK_lt {w : Nat} {cs : List Nat} (hb : ∀ j, cs.getD j 0 < 2 ^ w) (j : Nat) :
    (chunkPairK w cs).getD j 0 < 2 ^ (w + w) := by
  rw [chunkPairK_getD]
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le (hb _) (Nat.pow_le_pow_right (by decide) (by omega))),
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hb _) (Nat.pow_le_pow_right (by decide) (by omega)))]
  simp

theorem testBit_chunkJoinK : ∀ (k w : Nat) (cs : List Nat), (∀ j, cs.getD j 0 < 2 ^ w) →
    ∀ i < w * 2 ^ k, (chunkJoinK k w cs).testBit i = (cs.getD (i / w) 0).testBit (i % w)
  | 0, w, cs, _, i, hi => by
    have hw : i / w = 0 := Nat.div_eq_of_lt (by simpa using hi)
    rw [hw, Nat.mod_eq_of_lt (by simpa using hi)]
    cases cs <;> rfl
  | k + 1, w, cs, hb, i, hi => by
    have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
    have e : chunkJoinK (k + 1) w cs = chunkJoinK k (w + w) (chunkPairK w cs) := rfl
    have hk : (w + w) * 2 ^ k = w * 2 ^ (k + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc, Nat.mul_two]
    rw [e, testBit_chunkJoinK k (w + w) _ (chunkPairK_lt hb) i (hk ▸ hi),
      chunkPairK_getD, ← Nat.two_mul, Nat.mul_comm 2 w, ← Nat.div_div_eq_div_mul, Nat.mod_mul]
    have hr : i % w < w := Nat.mod_lt _ hw
    have hd := Nat.div_add_mod (i / w) 2
    rcases Nat.mod_two_eq_zero_or_one (i / w) with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero, Nat.testBit_or, Nat.testBit_shiftLeft]
      have : 2 * (i / w / 2) = i / w := by omega
      rw [this]
      have hn : ¬ w ≤ i % w := by omega
      simp [hn]
    · rw [h, Nat.mul_one, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le (hb _) (Nat.pow_le_pow_right (by decide) (by omega)))]
      have : 2 * (i / w / 2) + 1 = i / w := by omega
      rw [this]
      simp [Nat.add_sub_cancel]

theorem chunkStripK_getD : ∀ (cs : List Nat) (j : Nat),
    (chunkStripK cs).getD j 0 = cs.getD j 0 >>> 64
  | [], j => by simp [chunkStripK]
  | _ :: _, 0 => rfl
  | _ :: t, j + 1 => chunkStripK_getD t j

theorem testBit_chunkJoinK_strip (k w : Nat) (cs : List Nat) (hb : ∀ j, cs.getD j 0 >>> 64 < 2 ^ w)
    (i : Nat) (hi : i < w * 2 ^ k) :
    (chunkJoinK k w (chunkStripK cs)).testBit i = (cs.getD (i / w) 0).testBit (64 + i % w) := by
  rw [testBit_chunkJoinK k w _ (fun j => chunkStripK_getD cs j ▸ hb j) i hi, chunkStripK_getD,
    Nat.testBit_shiftRight]

end CFSG.KC.AxisPlane

end

namespace CertificateChecks.KernelAP

open Lean Elab Command CFSG.KC.Eval

meta def isTrue (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e (mkConst ``Bool.true)

meta def forallLt (P : Expr) (ps : Array Expr) : Expr := Id.run do
  let mut t := mkApp (mkConst ``forall_lt_zero') P
  for k in [0:ps.size] do
    t := mkAppN (mkConst ``forall_lt_succ') #[P, mkRawNatLit k, t, ps[k]!]
  return t

meta def natT : Expr := mkConst ``Nat
meta def listNat : Expr := mkApp (mkConst ``List [0]) natT
meta def getDN (l i : Expr) : Expr := mkApp4 (mkConst ``List.getD [0]) natT l i (mkRawNatLit 0)
meta def getDL (l i : Expr) : Expr :=
  mkApp4 (mkConst ``List.getD [0]) listNat l i (mkApp (mkConst ``List.nil [0]) natT)
meta def lengthE (α l : Expr) : Expr := mkApp2 (mkConst ``List.length [0]) α l

meta def listE (α : Expr) (es : Array Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) α e acc) (mkApp (mkConst ``List.nil [0]) α)

meta def lamN (body : Expr) : Expr := .lam `i natT body .default

meta def forallLtE (n body : Expr) : Expr :=
  .forallE `i natT (.forallE `h (mkApp4 (mkConst ``LT.lt [0]) natT (mkConst ``instLTNat) (.bvar 0) n)
    body .default) .default

meta partial def readE (e : Expr) : CoreM Val := do
  match e with
  | .lit (.natVal v) => return .nat v
  | .mdata _ e => readE e
  | .const n _ => readC n
  | .letE _ _ v b _ => readE (b.instantiate1 v)
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then return ← readE (e.getArg! 1)
    if e.isHeadBetaTarget then return ← readE e.headBeta
    let mut e := e
    let mut xs : Array Val := #[]
    repeat
      if e.isAppOfArity ``List.cons 3 then
        xs := xs.push (← readE (e.getArg! 1))
        e := e.getArg! 2
      else if let .letE _ _ v b _ := e then
        e := b.instantiate1 v
      else if e.isHeadBetaTarget then
        e := e.headBeta
      else if e.isAppOfArity ``List.nil 1 then
        return .list xs
      else
        throwError "#kc_planes: cannot read {e}"
    return .list xs
where
  readC (n : Name) : CoreM Val := do
    match (← getConstInfo n).value? (allowOpaque := true) with
    | some v => readE v
    | none => throwError "#kc_planes: {n} has no value"

meta partial def valTy (pre : Name) (v : Val) : CoreM Expr := do
  match v with
  | .nat _ | .chunks _ => return natT
  | .ref m => return (← getConstInfo (pre ++ m)).type
  | .list xs =>
    let t ← if h : 0 < xs.size then valTy pre xs[0] else pure natT
    return mkApp (mkConst ``List [0]) t

meta def planeChunkW : Nat := 8192

meta def planeChunks (n : Nat) : Array Nat := Id.run do
  let rec go : Nat → Nat → Array Nat → Array Nat
    | 0, m, acc => acc.push m
    | k + 1, m, acc => let s := planeChunkW <<< k; go k (m >>> s) (go k (m % (1 <<< s)) acc)
  let mut cs := go (Nat.log2 (n.log2 / planeChunkW) + 1) n #[]
  while cs.size > 1 && cs.back! == 0 do
    cs := cs.pop
  return cs

meta partial def planeTree (ls : Array Expr) (lo hi : Nat) : Expr :=
  if hi ≤ lo + 1 then ls[lo]! else
    let mid := (lo + hi) / 2
    mkApp2 (mkConst ``Nat.lor) (planeTree ls lo mid)
      (mkApp2 (mkConst ``Nat.shiftLeft) (planeTree ls mid hi) (mkRawNatLit (planeChunkW * (mid - lo))))

meta partial def valE (pre : Name) (v : Val) : CoreM Expr := do
  match v with
  | .nat n | .chunks n => return mkRawNatLit n
  | .ref m => return mkConst (pre ++ m)
  | .list xs =>
    let t ← if h : 0 < xs.size then valTy pre xs[0] else pure natT
    return listE t (← xs.mapM (valE pre))

meta def addV (pre n : Name) (v : Val) : CoreM Unit := do
  if let .nat x := v then
    if x ≥ 1 <<< (2 * planeChunkW) then
      let cs := planeChunks x
      let h := (hash (pre ++ n)).toNat
      let salt (i : Nat) : Nat := (h + (i + 1) * 11400714819323198485) % 18446744073709551616
      let ls := (Array.range cs.size).map fun i => mkApp2 (mkConst ``Nat.shiftRight)
        (mkRawNatLit ((cs[i]! <<< 64) ||| salt i)) (mkRawNatLit 64)
      addDecl (forceExpose := true) <| .defnDecl
        { name := pre ++ n, levelParams := [], type := natT, value := planeTree ls 0 ls.size,
          hints := .regular 0, safety := .safe }
      return
  addDecl (forceExpose := true) <| .defnDecl
    { name := pre ++ n, levelParams := [], type := ← valTy pre v, value := ← valE pre v,
      hints := .regular 0, safety := .safe }

meta def byDecide (p inst : Expr) : Expr :=
  mkApp3 (mkConst ``of_decide_eq_true) p inst (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool)
    (mkConst ``Bool.true))

end CertificateChecks.KernelAP

open Lean Elab Command CFSG.KC.Eval CertificateChecks.KernelAP in
elab "#kc_planes " pre:ident out:ident lamsI:ident sizesI:ident rowsI:ident* : command => do
  let P := pre.getId
  let X := P ++ out.getId
  let res (i : Ident) : CommandElabM Name := do
    let n := if (← getEnv).contains (P ++ i.getId) then P ++ i.getId else i.getId
    liftCoreM <| realizeGlobalConstNoOverload (mkIdent n)
  let lamsN ← res lamsI
  let sizesN ← res sizesI
  let rowsN ← rowsI.mapM res
  liftCoreM <| withOptions (Elab.async.set · false) do
    let t0 ← IO.monoNanosNow
    let lamsV ← readE.readC lamsN
    let sizesV ← readE.readC sizesN
    let mut args : Array Val := #[lamsV]
    for r in rowsN do
      args := args.push (← readE.readC r)
    let outs ← match planeStep args with
      | .error e => throwError "#kc_planes {X}: {e}"
      | .ok o => pure o
    for (n, v) in outs do
      addV X n v
    let t1 ← IO.monoNanosNow
    let ms (a b : Nat) : Float := (b - a).toFloat / 1e6
    logInfo m!"PLANES {X} data {ms t0 t1} ms"
    let nl := match outs.find? (fun (n, _) => n == `Ls) with
      | some (_, .list xs) => xs.size
      | _ => 0
    let m := rowsN.size
    let n ← match lamsV with
      | .list xs => pure xs.size
      | _ => throwError "#kc_planes: lams"
    let sizesL ← match sizesV with
      | .list xs => xs.mapM fun x => match x with | .nat k => pure k | _ => throwError "sizes"
      | _ => throwError "#kc_planes: sizes"
    let c (s : String) : Expr := mkConst (X ++ Name.mkSimple s)
    let thm (s : String) (ty : Expr) : CoreM Expr := do
      let name := X ++ Name.mkSimple s
      let a ← IO.monoNanosNow
      CFSG.KC.addThmDecl ({ name, levelParams := [], type := ty, value := Lean.reflBoolTrue })
      let b ← IO.monoNanosNow
      logInfo m!"CHECK {name} {ms a b} ms"
      return mkConst name
    let ap := fun (f : Name) (xs : Array Expr) => mkAppN (mkConst (`CFSG.KC.AxisPlane ++ f)) xs
    let mut okP := #[]
    let mut invP := #[]
    let mut imgP := #[]
    let boolT := mkConst ``Bool
    let band (a b : Expr) : Expr :=
      mkApp4 (mkConst ``Bool.rec [1]) (.lam `x boolT boolT .default) (mkConst ``Bool.false) b a
    for g in [0:m] do
      okP := okP.push (← thm s!"ok{g}" (isTrue (ap `opsOK #[c s!"ops{g}", mkConst rowsN[g]!])))
      let cs : Array Expr :=
        ((Array.range nl).map fun b => ap `invK #[c s!"ops{g}", c s!"L{b}"]) ++
        ((Array.range 5).map fun j => ap `imgEqK #[c s!"ops{g}", c s!"Q{j}", c s!"R{g}_{j}"])
      let chunk := 4
      let mut ps : Array Expr := #[]
      for k in [0:(cs.size + chunk - 1) / chunk] do
        let grp := cs.extract (k * chunk) (min cs.size ((k + 1) * chunk))
        let mut tails : Array Expr := #[grp.back!]
        for i' in [0:grp.size - 1] do
          tails := tails.push (band grp[grp.size - 2 - i']! tails.back!)
        tails := tails.reverse
        let mut p ← thm s!"all{g}_{k}" (isTrue tails[0]!)
        for i in [0:grp.size] do
          if i + 1 < grp.size then
            ps := ps.push (mkApp3 (mkConst ``bandL) grp[i]! tails[i + 1]! p)
            p := mkApp3 (mkConst ``bandR) grp[i]! tails[i + 1]! p
          else
            ps := ps.push p
      invP := invP.push (ps.extract 0 nl)
      imgP := imgP.push (ps.extract nl (nl + 5))
    let genP ← thm "gen" (isTrue (ap `genK #[c "Qs", c "Rss"]))
    let covP ← thm "cov" (isTrue (ap `covK #[c "Ls", c "Qs"]))
    let seedsP ← thm "seeds" (isTrue (ap `seedsK #[c "Ls", c "Qs", mkConst lamsN]))
    let d0P ← thm "d0" (isTrue (ap `d0K #[c "Qs", mkConst lamsN]))
    let mut cntP := #[]
    for r in [0:n] do
      cntP := cntP.push (← thm s!"cnt{r}"
        (isTrue (ap `cntK #[c "Ls", mkRawNatLit (r + 1), mkRawNatLit (sizesL[r]!)])))
    let opssE := c "opss"
    let rlsE := listE listNat (rowsN.map mkConst)
    let LsE := c "Ls"
    let QsE := c "Qs"
    let RssE := c "Rss"
    let lamsE := mkConst lamsN
    let sizesE := mkConst sizesN
    let opsG := getDL opssE (.bvar 0)
    let invBody (g : Expr) := forallLtE (lengthE natT LsE)
      (isTrue (ap `invK #[getDL opssE g, getDN LsE (.bvar 1)]))
    let imgBody (g : Expr) := forallLtE (lengthE natT QsE)
      (isTrue (ap `imgEqK #[getDL opssE g, getDN QsE (.bvar 1), getDN (getDL RssE g) (.bvar 1)]))
    let invAll := forallLt (lamN (invBody (.bvar 2)))
      ((Array.range m).map fun g => forallLt (lamN (isTrue (ap `invK #[getDL opssE (mkRawNatLit g),
        getDN LsE (.bvar 0)]))) invP[g]!)
    let imgAll := forallLt (lamN (imgBody (.bvar 2)))
      ((Array.range m).map fun g => forallLt (lamN (isTrue (ap `imgEqK #[getDL opssE (mkRawNatLit g),
        getDN QsE (.bvar 0), getDN (getDL RssE (mkRawNatLit g)) (.bvar 0)]))) imgP[g]!)
    let okAll := forallLt (lamN (isTrue (ap `opsOK #[opsG, getDL rlsE (.bvar 0)]))) okP
    let lenE (α l : Expr) := lengthE α l
    let eqN (a b : Expr) := mkApp3 (mkConst ``Eq [1]) natT a b
    let reflN (a : Expr) := mkApp2 (mkConst ``Eq.refl [1]) natT a
    let imgLen := forallLt (lamN (eqN (lenE natT (getDL RssE (.bvar 0))) (lenE natT QsE)))
      ((Array.range m).map fun g => reflN (lenE natT (getDL RssE (mkRawNatLit g))))
    let cntAll := forallLt (lamN (isTrue (ap `cntK #[LsE,
      mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) natT natT natT
        (mkApp2 (mkConst ``instHAdd [0]) natT (mkConst ``instAddNat)) (.bvar 0) (mkRawNatLit 1),
      getDN sizesE (.bvar 0)]))) cntP
    let ltE (a b : Expr) := mkApp4 (mkConst ``LT.lt [0]) natT (mkConst ``instLTNat) a b
    let qsPos := byDecide (ltE (mkRawNatLit 0) (lenE natT QsE)) (mkApp2 (mkConst ``Nat.decLt) (mkRawNatLit 0) (lenE natT QsE))
    let powE := mkApp2 (mkConst ``Nat.pow) (mkRawNatLit 2) (lenE natT LsE)
    let lamsLt := byDecide (ltE (lenE natT lamsE) powE) (mkApp2 (mkConst ``Nat.decLt) (lenE natT lamsE) powE)
    let lenSizes := byDecide (eqN (lenE natT sizesE) (lenE natT lamsE))
      (mkApp2 (mkConst ``instDecidableEqNat) (lenE natT sizesE) (lenE natT lamsE))
    let lenRss := reflN (lenE listNat RssE)
    let ty := ap `PlanesChk #[opssE, rlsE, LsE, QsE, RssE, lamsE, sizesE]
    let val := mkAppN (mkConst ``CFSG.KC.AxisPlane.PlanesChk.mk)
      #[opssE, rlsE, LsE, QsE, RssE, lamsE, sizesE, lenRss, okAll, invAll, imgLen, imgAll, genP, covP,
        seedsP, d0P, qsPos, lamsLt, lenSizes, cntAll]
    let a ← IO.monoNanosNow
    CFSG.KC.addThmDecl ({ name := X ++ `chk, levelParams := [], type := ty, value := val })
    let b ← IO.monoNanosNow
    logInfo m!"CHECK {X ++ `chk} {ms a b} ms; total {ms t0 b} ms"

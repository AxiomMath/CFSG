module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Data.CFSGNative.MonsterAxis.Cover
public import Certificates.Kernel.AxisPlane.Letters
public import Batteries.Data.List.Basic
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

open Lean Elab Command Meta

namespace CertificateChecks.KernelAP.Words

open CertificateChecks.KernelAP

meta def natT : Expr := mkConst ``Nat
meta def listNatT : Expr := mkApp (mkConst ``List [0]) natT
meta def arrNatT : Expr := mkApp (mkConst ``Array [0]) natT
meta def genT : Expr := mkConst ``CFSG.Monster.AxisCount.Native.Gen
meta def wordT : Expr := mkApp (mkConst ``List [0]) genT
meta def msT : Expr := mkApp (mkConst ``List [0]) arrNatT

meta def listE (α : Expr) (es : Array Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) α e acc) (mkApp (mkConst ``List.nil [0]) α)

meta def natOf (e : Expr) : MetaM Nat := do
  let e := e.consumeMData
  if let .lit (.natVal n) := e then return n
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if let .lit (.natVal n) := (e.getArg! 1).consumeMData then return n
  throwError "#kc_words: not a numeral: {e}"

meta partial def unlet (e : Expr) : Expr :=
  match e.consumeMData with
  | .letE _ _ v b _ => unlet (b.instantiate1 v)
  | e => e

meta def elems (e : Expr) : MetaM (Array (Expr × Expr)) := do
  let mut e := unlet e
  let mut xs := #[]
  repeat
    if e.isAppOfArity ``List.cons 3 then
      let t := unlet (e.getArg! 2)
      xs := xs.push (unlet (e.getArg! 1), t)
      e := t
    else if e.isAppOfArity ``List.nil 1 then
      return xs
    else
      throwError "#kc_words: not a list literal: {e}"
  return xs

meta def keyOf (f : Name) (g : Expr) : MetaM (Nat × String) := do
  if g.isAppOfArity f 1 then return (0, s!"{← natOf (g.getArg! 0)}")
  if g.isAppOfArity ``CFSG.Monster.AxisCount.Native.Gen.sign 1 then
    return (1, s!"s{← natOf (g.getArg! 0)}")
  if g.isConstOf ``CFSG.Monster.AxisCount.Native.Gen.xi then return (2, "x")
  if g.isAppOfArity ``CFSG.Monster.AxisCount.Native.Gen.rho 1 then return (3, "i")
  throwError "#kc_words: unexpected letter {g}"

meta def field (src fld : Name) : MetaM (Expr × Expr × Nat) := do
  let some v := (← getConstInfo src).value? (allowOpaque := true)
    | throwError "#kc_words: {src} has no value"
  let v := v.consumeMData
  let .const ctor _ := v.getAppFn | throwError "#kc_words: {src} is not a structure value"
  let .ctorInfo ci ← getConstInfo ctor | throwError "#kc_words: {src} is not a structure value"
  let S := ci.induct
  let fs := getStructureFields (← getEnv) S
  let some j := fs.findIdx? (· == fld) | throwError "#kc_words: {S} has no field {fld}"
  let a := unlet (v.getArg! (ci.numParams + j))
  let proj := mkApp (mkConst (S ++ fld)) (mkConst src)
  if a.isAppOfArity ``List.toArray 2 then return (proj, unlet (a.getArg! 1), 2)
  if (a.isAppOfArity ``List.cons 3 || a.isAppOfArity ``List.nil 1) && (a.getArg! 0).isAppOf ``List then
    return (proj, a, 1)
  return (proj, a, 0)

meta def words (a : Expr) (s : Nat) : MetaM (Array Expr) := do
  if s == 0 then return #[a]
  return (← elems a).map (·.1)

meta def addDef (name : Name) (ty v : Expr) : MetaM Unit :=
  addDecl (forceExpose := true) <| .defnDecl
    { name, levelParams := [], type := ty, value := v, hints := .regular 0, safety := .safe }

meta def addThm (name : Name) (v : Expr) (ty? : Option Expr := none) : MetaM Float := do
  let ty ← match ty? with
    | some t => pure t
    | none => inferType v
  let a ← IO.monoNanosNow
  CFSG.KC.addThmDecl ({ name, levelParams := [], type := ty, value := v })
  let b ← IO.monoNanosNow
  return (b - a).toFloat / 1e6

end CertificateChecks.KernelAP.Words

open CertificateChecks.KernelAP CertificateChecks.KernelAP.Words in
elab "#kc_letters " tI:ident fI:ident hRI:ident hVI:ident srcs:ident* " with " flds:ident+ :
    command => do
  let T := tI.getId
  let f ← liftCoreM <| realizeGlobalConstNoOverload fI
  let hR ← liftCoreM <| realizeGlobalConstNoOverload hRI
  let hV ← liftCoreM <| realizeGlobalConstNoOverload hVI
  let srcNs ← srcs.mapM fun s => liftCoreM <| realizeGlobalConstNoOverload s
  liftTermElabM <| withOptions (Elab.async.set · false) do
    let t0 ← IO.monoNanosNow
    let mut seen : Std.HashSet String := {}
    let mut lets : Array (Nat × String × Expr) := #[]
    for src in srcNs do
      for fld in flds do
        let (_, a, s) ← field src fld.getId
        for w in ← words a s do
          for (g, _) in ← elems w do
            let (c, k) ← keyOf f g
            unless seen.contains k do
              seen := seen.insert k
              lets := lets.push (c, k, g)
    let mut total : Float := 0
    let mut evalT : Float := 0
    let mut np : Nat := 0
    let fV ← unsafe evalConst (Nat → CFSG.Monster.AxisCount.Native.Gen) f
    for (c, k, g) in lets do
      let e0 ← IO.monoNanosNow
      let gV : CFSG.Monster.AxisCount.Native.Gen ←
        if c == 0 then pure (fV (← natOf (g.getArg! 0)))
        else if c == 1 then pure (.sign (← natOf (g.getArg! 0)))
        else if c == 2 then pure .xi
        else pure (.rho (false, 0, 0))
      let m := gV.l2Rows.toList
      let e1 ← IO.monoNanosNow
      evalT := evalT + (e1 - e0).toFloat / 1e6
      let mN := T ++ Name.mkSimple s!"m{k}"
      addDef mN listNatT (listE natT (m.toArray.map mkRawNatLit))
      let l := mkConst mN
      if c == 0 then
        np := np + 1
        let kE := g.getArg! 0
        total := total + (← addThm (T ++ Name.mkSimple s!"r{k}")
          (mkAppN (mkConst hR) #[kE, l, reflBoolTrue]))
        total := total + (← addThm (T ++ Name.mkSimple s!"v{k}")
          (mkAppN (mkConst hV) #[kE, reflBoolTrue]))
      else if c == 3 then
        total := total + (← addThm (T ++ `rho)
          (mkAppN (mkConst ``l2Rows_rho) #[g.getArg! 0, l, reflBoolTrue]))
      else
        total := total + (← addThm (T ++ Name.mkSimple s!"r{k}")
          (mkAppN (mkConst ``l2Rows_of) #[g, l, reflBoolTrue]))
    let t1 ← IO.monoNanosNow
    logInfo m!"LETTERS {T}: {lets.size} letters ({np} permutations), matrices {evalT} ms, checks {total} ms, total {(t1 - t0).toFloat / 1e6} ms"

open CertificateChecks.KernelAP CertificateChecks.KernelAP.Words in
elab "#kc_words " xI:ident tI:ident fI:ident srcI:ident " with " flds:ident+ : command => do
  let X := xI.getId
  let T := tI.getId
  let f ← liftCoreM <| realizeGlobalConstNoOverload fI
  let src ← liftCoreM <| realizeGlobalConstNoOverload srcI
  liftTermElabM <| withOptions (Elab.async.set · false) do
    let t0 ← IO.monoNanosNow
    let tc (s : String) : Expr := mkConst (T ++ Name.mkSimple s)
    let wordProof (w : Expr) : MetaM (Expr × Expr) := do
      let xs ← elems w
      let mut ms : Expr := mkApp (mkConst ``List.nil [0]) arrNatT
      let mut pM : Expr := mkConst ``map_nil
      let mut pA : Expr := mkConst ``all_nil
      for (g, tl) in xs.reverse do
        let (c, k) ← keyOf f g
        let m := mkApp2 (mkConst ``List.toArray [0]) natT (tc s!"m{k}")
        let (h₁, hv) :=
          if c == 0 then (tc s!"r{k}", tc s!"v{k}")
          else if c == 1 then (tc s!"r{k}", mkApp (mkConst ``isVis_sign) (g.getArg! 0))
          else if c == 2 then (tc "rx", mkConst ``isVis_xi)
          else (mkApp (tc "rho") (g.getArg! 0), mkApp (mkConst ``isVis_rho) (g.getArg! 0))
        pM := mkAppN (mkConst ``map_cons) #[g, tl, m, ms, h₁, pM]
        pA := mkAppN (mkConst ``all_cons) #[g, tl, hv, pA]
        ms := mkApp3 (mkConst ``List.cons [0]) arrNatT m ms
      return (ms, mkAppN (mkConst ``WordM.of) #[w, ms, pM, pA])
    let wordM := mkConst ``WordM
    let mut total : Float := 0
    for fld in flds do
      let (proj, a, s) ← field src fld.getId
      let mN := X ++ fld.getId.appendAfter "_m"
      let thmN := X ++ fld.getId
      if s == 0 then
        let (ms, p) ← wordProof a
        addDef mN msT ms
        total := total + (← addThm thmN p (some (mkApp2 wordM proj (mkConst mN))))
      else
        let ws ← elems a
        let msLT := mkApp (mkConst ``List [0]) msT
        let mut mss : Expr := mkApp (mkConst ``List.nil [0]) msT
        let mut pF : Expr := mkAppN (mkConst ``List.Forall₂.nil [0, 0]) #[wordT, msT, wordM]
        for (w, tl) in ws.reverse do
          let (ms, p) ← wordProof w
          pF := mkAppN (mkConst ``List.Forall₂.cons [0, 0])
            #[wordT, msT, wordM, w, ms, tl, mss, p, pF]
          mss := mkApp3 (mkConst ``List.cons [0]) msT ms mss
        addDef mN msLT mss
        let lhs := if s == 2 then mkApp2 (mkConst ``Array.toList [0]) wordT proj else proj
        let ty := mkAppN (mkConst ``List.Forall₂ [0, 0]) #[wordT, msT, wordM, lhs, mkConst mN]
        total := total + (← addThm thmN pF (some ty))
    let t1 ← IO.monoNanosNow
    logInfo m!"WORDS {X}: checks {total} ms, total {(t1 - t0).toFloat / 1e6} ms"

module

public meta import Lean

open Lean Elab Command

elab "#b4_kval " n:ident " := " t:term : command => do
  let name := (← getCurrNamespace) ++ n.getId
  let e ← liftTermElabM do
    let e ← Term.elabTerm t (some (mkConst ``Nat))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  if e.hasMVar then throwError "#b4_kval {name}: the term has metavariables"
  liftCoreM <| withOptions (Elab.async.set · false) do
    let t0 ← IO.monoNanosNow
    match Kernel.whnf (← getEnv) {} e with
    | .ok (.lit (.natVal v)) =>
      addDecl (forceExpose := true) <| .defnDecl
        { name, levelParams := [], type := mkConst ``Nat, value := mkRawNatLit v,
          hints := .regular 0, safety := .safe }
      let ms := ((← IO.monoNanosNow) - t0).toFloat / 1e6
      logInfo m!"KVAL {name} {v.log2 + 1} bits, {ms} ms"
    | .ok r => throwError "#b4_kval {name}: no literal, got {r}"
    | .error ex => throwKernelException ex

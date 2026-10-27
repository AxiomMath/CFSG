module
public import CFSG.Sporadic.HNSchreier.PackedKernelBytes
public import CFSG.Sporadic.HNSchreier.ArchiveKernelData
public meta import Lean.Elab.Term
public meta import Lean.Meta.Tactic.AuxLemma

public section
namespace CFSG.Sporadic.HNSchreier.KernelBytes

theorem append_packed_bytes (A B : KernelBytes) (l r a b n : Nat)
    (hAl : A.size = l) (hBr : B.size = r)
    (hA : A.bytes = (packed l a).bytes) (hB : B.bytes = (packed r b).bytes)
    (ha : a < (1 <<< (8*l))) (hn : a + (b <<< (8*l)) = n) :
    (appendSized l r A B hAl hBr).bytes = (packed (l+r) n).bytes := by
  have hp : (1 <<< (8*l)) = 256 ^ l := by
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_mul]
  have hs : (b <<< (8*l)) = b * 256 ^ l := by
    rw [Nat.shiftLeft_eq, Nat.pow_mul]
  rw [hs] at hn
  rw [hp] at ha
  change A.bytes ++ B.bytes = _
  rw [hA, hB, ← hn, packed_append_bytes l r a b ha]

end CFSG.Sporadic.HNSchreier.KernelBytes

public meta section
open Lean Meta Elab Term
open CFSG.Sporadic.HNSchreier

private def packedExpr (w n : Nat) : Expr :=
  mkApp2 (mkConst ``KernelBytes.packed) (mkNatLit w) (mkNatLit n)

private partial def packArchive (e : Expr) (proof : Bool) : MetaM (Nat × Nat × Expr) := do
  let e := e.consumeMData
  let args := e.getAppArgs
  if e.getAppFn.isConstOf ``KernelBytes.packed then
    let some w := args[0]!.nat? | throwError "nonliteral packed width"
    let some n := args[1]!.nat? | throwError "nonliteral packed value"
    return (w, n, ← mkEqRefl (mkApp (mkConst ``KernelBytes.bytes) e))
  unless e.getAppFn.isConstOf ``KernelBytes.appendSized do
    throwError "unexpected archive constructor: {e.getAppFn}"
  let (l, a, hA) ← packArchive args[2]! proof
  let (r, b, hB) ← packArchive args[3]! proof
  let n := a + (b <<< (8*l))
  if !proof then return (l+r, n, mkConst ``True.intro)
  let rhs := mkApp2 (mkConst ``Nat.shiftLeft) (mkNatLit 1) (mkNatLit (8*l))
  let prop := mkApp2 (mkConst ``Nat.lt) (mkNatLit a) rhs
  let inst := mkApp2 (mkConst ``Nat.decLt) (mkNatLit a) rhs
  let bound := mkApp3 (mkConst ``of_decide_eq_true) prop inst
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
  let h := mkAppN (mkConst ``KernelBytes.append_packed_bytes)
    #[args[2]!, args[3]!, mkNatLit l, mkNatLit r, mkNatLit a, mkNatLit b, mkNatLit n,
      args[4]!, args[5]!, hA, hB, bound, ← mkEqRefl (mkNatLit n)]
  return (l+r, n, h)

private def archiveBody : MetaM Expr := do
  let info ← getConstInfo ``Native.archiveKernelBytes
  return info.value!.betaRev #[mkConst ``Unit.unit]

elab "giant_archive%" : term => do
  let started ← IO.monoMsNow
  let (w, n, _) ← packArchive (← archiveBody) false
  logInfo m!"Packed {w} archive bytes into one Nat in {(← IO.monoMsNow)-started}ms"
  return mkApp2 (mkConst ``KernelBytes.packedFast) (mkNatLit w) (mkNatLit n)

elab "giant_archive_eq%" : term <= expectedType => do
  let started ← IO.monoMsNow
  let (_, _, h) ← packArchive (← archiveBody) true
  logInfo m!"Constructed exact giant-Nat archive equivalence in {(← IO.monoMsNow)-started}ms"
  let expected := expectedType
  let name ← withOptions (Elab.async.set · false) do
    mkAuxLemma [] expected h
  logInfo m!"Kernel checked exact giant-Nat archive equivalence in {(← IO.monoMsNow)-started}ms"
  return mkConst name
end

module

public import CFSG.Certificates.Kernel.Common.LceS
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public import Lean.Exception

public section

namespace CertificateChecks.KernelCo2

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem beq_join (f : List Nat → Nat → Nat)
    (hf : ∀ l1 l2 x, f (List.append l1 l2) x = f l2 (f l1 x)) (l1 l2 : List Nat) (x y z : Nat)
    (h1 : Nat.beq (f l1 x) y = true) (h2 : Nat.beq (f l2 y) z = true) :
    Nat.beq (f (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [hf, h1, h2]

theorem runFacts_append (blk WT : Nat → Nat) (INV nC L : Nat) :
    ∀ l1 l2 x, runFacts blk WT INV nC L (List.append l1 l2) x =
      runFacts blk WT INV nC L l2 (runFacts blk WT INV nC L l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (runChunk blk WT INV nC L C x) (runFacts blk WT INV nC L (List.append l1 l2)) =
      runFacts blk WT INV nC L l2 (strictN (runChunk blk WT INV nC L C x) (runFacts blk WT INV nC L l1))
    rw [strictN_eq, strictN_eq, runFacts_append blk WT INV nC L l1 l2]

theorem runCover_append (blk LVs : Nat → Nat) (nf L : Nat) :
    ∀ l1 l2 x, runCover blk LVs nf L (List.append l1 l2) x =
      runCover blk LVs nf L l2 (runCover blk LVs nf L l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (covChunk blk LVs nf L C x) (runCover blk LVs nf L (List.append l1 l2)) =
      runCover blk LVs nf L l2 (strictN (covChunk blk LVs nf L C x) (runCover blk LVs nf L l1))
    rw [strictN_eq, strictN_eq, runCover_append blk LVs nf L l1 l2]

end CertificateChecks.KernelCo2

namespace CertificateChecks.KernelCo2.Join

open Lean Elab Command

meta def parts (ty : Expr) : Option (Expr × Expr × Expr × Expr) := do
  let some (_, lhs, _) := ty.eq? | none
  guard (lhs.isAppOfArity ``Nat.beq 2)
  let a := lhs.appFn!.appArg!
  let y := lhs.appArg!
  guard a.isApp
  guard a.appFn!.isApp
  return (a.appFn!.appFn!, a.appFn!.appArg!, a.appArg!, y)

meta partial def tree (f hf : Expr) (sl : Array (Expr × Expr × Expr × Expr)) (lo hi : Nat) :
    Expr × Expr × Expr × Expr :=
  if hi = lo + 1 then sl[lo]!
  else
    let mid := lo + (hi - lo) / 2
    let (p1, l1, x, _) := tree f hf sl lo mid
    let (p2, l2, _, z) := tree f hf sl mid hi
    let y := (sl[mid]!).2.2.1
    (mkAppN (mkConst ``CertificateChecks.KernelCo2.beq_join) #[f, hf, l1, l2, x, y, z, p1, p2],
      mkApp3 (mkConst ``List.append [Level.zero]) (mkConst ``Nat) l1 l2, x, z)

meta def joinCmd (nm law : Name) (ts : Array Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut sl : Array (Expr × Expr × Expr × Expr) := #[]
  let mut fE : Option Expr := none
  for t in ts do
    let some ci := env.find? t | throwError "unknown theorem {t}"
    let some (f, l, x, y) := parts ci.type | throwError "{t}: not a slice check"
    if let some f0 := fE then
      unless f0 == f do throwError "{t}: another loop function"
    fE := some f
    sl := sl.push (mkConst t, l, x, y)
  let some f := fE | throwError "no slices"
  let law ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent law)
  let nm := (← getCurrNamespace) ++ nm
  let hf := mkAppN (mkConst law) f.getAppArgs
  let (p, L, x, z) := tree f hf sl 0 sl.size
  let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
    (mkApp2 (mkConst ``Nat.beq) (mkApp2 f L x) z) (mkConst ``Bool.true)
  liftCoreM <| withOptions (Elab.async.set · false) <|
    CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := p }

end CertificateChecks.KernelCo2.Join

open CertificateChecks.KernelCo2.Join in
elab "#kc_join " nm:ident law:ident ts:ident* : command =>
  joinCmd nm.getId law.getId (ts.map (·.getId))

open CertificateChecks.KernelCo2.Join in
elab "#kc_join_range " nm:ident law:ident pre:ident base:str lo:num hi:num : command =>
  joinCmd nm.getId law.getId <| ((List.range (hi.getNat + 1 - lo.getNat)).map fun k =>
    pre.getId ++ Lean.Name.mkSimple s!"{base.getString}{lo.getNat + k}").toArray

end

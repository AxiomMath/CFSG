module

public import Certificates.Data.CFSGNative.Timmesfeld.Fi24Three
public import Std.Data.HashMap

public section

namespace CFSG.HardMathSupport.Dickson.I271.Fi24Twin.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native

set_option compiler.extract_closed false

@[expose] def twFixPts (s : Table) : Array Nat := (Array.range nPts).filter fun i => ap s i == i

@[expose] def twPosOf (F : Array Nat) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate nPts 0
  for c in [0:F.size] do
    r := r.set! F[c]! c
  return r

@[expose] def twRows (c : Ctx) (F : Array Nat) : Array (Array Bool) :=
  (Array.range F.size).map fun i =>
    let v := vecOf c F F[i]!
    (Array.range F.size).map fun j => j != i && v[j]!

@[expose] def twImg2 (c : Ctx) (a b : Nat) (q : Array Nat) : Array Nat :=
  clsAtN c.O c.bInv c.pl c.tP a (clsAtN c.O c.bInv c.pl c.tP b q)

@[expose] def twProdTab (c : Ctx) (F posF : Array Nat) (a b : Nat) : Array Nat :=
  (twImg2 c a b F).map fun q => posF[q]!

@[expose] def twinVerifyAux (c : Ctx) (w : List Nat) (F posF : Array Nat) (R : Array (Array Bool))
    (sigs : Array (Array Nat)) (third : Array Nat) (prs : Array (Nat × Nat)) (pind : Array Nat)
    (U : Array (Array Nat)) (uidx : Array Nat) (gam : Array (Array Nat)) (zi : Array Nat) :
    Bool :=
  let m := F.size
  let nP := prs.size
  let nU := U.size
  w.all (fun l => decide (l < c.L.size)) &&
    allIn 0 m (fun i => posF[F[i]!]! == i) &&
    prs.all (fun e => decide (e.1 < m) && decide (e.2 < m) && e.1 != e.2 && R[e.1]! == R[e.2]!) &&
    allIn 0 m (fun i => allIn 0 m (fun j => i == j || R[i]! != R[j]! ||
      (decide (pind[i * m + j]! < nP) && prs[pind[i * m + j]!]! == (i, j)))) &&
    allIn 0 m (fun i => prs.any fun e => e.1 == i) &&
    allIn 0 nP (fun p => decide (uidx[p]! < nU) &&
      twProdTab c F posF F[prs[p]!.1]! F[prs[p]!.2]! == U[uidx[p]!]!) &&
    allIn 0 nP (fun p =>
      let e := prs[p]!
      let t := third[p]!
      let sg := sigs[p]!
      allIn 0 nP (fun q => sg != sigs[q]! || prs[q]! == e || prs[q]! == (e.2, t) ||
        prs[q]! == (t, e.1))) &&
    allIn 0 nU (fun u =>
      let Tu := U[u]!
      allIn 0 nU (fun v =>
        let Tv := U[v]!
        let Z := gam[zi[u * nU + v]!]!
        decide (zi[u * nU + v]! < gam.size) &&
          allIn 0 m (fun d => Tu[Tv[d]!]! == Z[Tv[Tu[d]!]!]!))) &&
    gam.all (fun Z => allIn 0 m (fun d => decide (Z[d]! < m)) &&
      U.all (fun T => allIn 0 m (fun d => Z[T[d]!]! == T[Z[d]!]!)))

@[expose] def twinVerify (c : Ctx) (w : List Nat) (sp : Array Nat)
    (prs : Array (Nat × Nat)) (pind : Array Nat) (U : Array (Array Nat)) (uidx : Array Nat)
    (gam : Array (Array Nat)) (zi : Array Nat) : Bool :=
  let F := twFixPts (wordTab c w)
  let posF := twPosOf F
  twinVerifyAux c w F posF (twRows c F) (prs.map fun e => twImg2 c F[e.1]! F[e.2]! sp)
    (prs.map fun e => posF[clsPt c F[e.1]! F[e.2]!]!) prs pind U uidx gam zi

@[expose] def twMkPairs (R : Array (Array Bool)) : Array (Nat × Nat) := Id.run do
  let m := R.size
  let mut r : Array (Nat × Nat) := #[]
  for i in [0:m] do
    let Ri := R[i]!
    for j in [0:m] do
      if i != j && Ri == R[j]! then
        r := r.push (i, j)
  return r

@[expose] def twMkPind (m : Nat) (prs : Array (Nat × Nat)) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate (m * m) 0
  for p in [0:prs.size] do
    r := r.set! (prs[p]!.1 * m + prs[p]!.2) p
  return r

@[expose] def twMkTabs (c : Ctx) (F posF : Array Nat) (prs : Array (Nat × Nat)) :
    Array (Array Nat) × Array Nat := Id.run do
  let mut U : Array (Array Nat) := #[]
  let mut seen : Std.HashMap (Array Nat) Nat := ∅
  let mut uidx : Array Nat := #[]
  for e in prs do
    let T := twProdTab c F posF F[e.1]! F[e.2]!
    match seen[T]? with
    | some u => uidx := uidx.push u
    | none =>
      seen := seen.insert T U.size
      uidx := uidx.push U.size
      U := U.push T
  return (U, uidx)

@[expose] def twInvIdx (m : Nat) (T : Array Nat) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate m 0
  for d in [0:m] do
    r := r.set! T[d]! d
  return r

@[expose] def twCompIdx (m : Nat) (P Q : Array Nat) : Array Nat :=
  (Array.range m).map fun d => P[Q[d]!]!

@[expose] def twMkGam (m : Nat) (U : Array (Array Nat)) (ab : Bool) :
    Array (Array Nat) × Array Nat := Id.run do
  let nU := U.size
  if ab then
    return (#[Array.range m], Array.replicate (nU * nU) 0)
  let mut gam : Array (Array Nat) := #[]
  let mut seen : Std.HashMap (Array Nat) Nat := ∅
  let mut zi : Array Nat := Array.replicate (nU * nU) 0
  for u in [0:nU] do
    for v in [0:nU] do
      let Z := twCompIdx m (twCompIdx m U[u]! U[v]!) (twInvIdx m (twCompIdx m U[v]! U[u]!))
      match seen[Z]? with
      | some k => zi := zi.set! (u * nU + v) k
      | none =>
        seen := seen.insert Z gam.size
        zi := zi.set! (u * nU + v) gam.size
        gam := gam.push Z
  return (gam, zi)

@[expose] def twinCheck (c : Ctx) (w : List Nat) (sp : Array Nat) (ab : Bool) : Bool :=
  let s := wordTab c w
  let F := twFixPts s
  let posF := twPosOf F
  let R := twRows c F
  let prs := twMkPairs R
  let pind := twMkPind F.size prs
  let tabs := twMkTabs c F posF prs
  let gz := twMkGam F.size tabs.1 ab
  twinVerify c w sp prs pind tabs.1 tabs.2 gz.1 gz.2

end CFSG.HardMathSupport.Dickson.I271.Fi24Twin.Native

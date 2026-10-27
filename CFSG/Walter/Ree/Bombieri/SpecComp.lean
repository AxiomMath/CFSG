module

public import CFSG.Walter.Ree.Bombieri.MatrixDef
public import CFSG.Walter.Ree.Bombieri.FastMul
public import CFSG.Walter.Ree.Bombieri.AppCheck

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

open F3P

abbrev D : ℕ := 114

@[expose] def ofCode (n : ℕ) : F3P :=
  let rec go : ℕ → ℕ → ℕ → ℕ → ℕ → F3P
    | 0, _, _, p, q => ⟨p, q⟩
    | fuel + 1, n, i, p, q =>
      if n = 0 then ⟨p, q⟩ else
      if n % 3 = 1 then go fuel (n / 3) (i + 1) (p ||| 1 <<< i) q
      else if n % 3 = 2 then go fuel (n / 3) (i + 1) p (q ||| 1 <<< i)
      else go fuel (n / 3) (i + 1) p q
  go 64 n 0 0 0

section

variable (T : Tab)

@[expose] def invT (a : F3P) : F3P :=
  let la := T.logT.getD (idx T.m a) 0
  if la < T.q1 && T.expT.getD la zero == a then T.expT.getD ((T.q1 - la) % T.q1) zero
  else invMod T.f T.m a

@[expose] def unitT (a : F3P) : Bool := mulT T a (normalize (invT T a)) == one

@[expose] def sumL (l : List F3P) : F3P := l.foldl add zero

@[expose] def prodT (l : List F3P) : F3P := l.foldl (mulT T) one

@[expose] def horner : List F3P → F3P → F3P
  | [], _ => zero
  | a :: l, x => add a (mulT T x (horner l x))

@[expose] def ptVarsF (c0 c1 c2 c3 t : F3P) : ℕ → F3P
  | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3 | 4 => t | _ => zero

@[expose] def atomsF (ρ : ℕ → F3P) : ℕ → F3P :=
  let av := ((List.range 7).map fun j => (Elim.atomDef j).evalM (mulT T) ρ fun _ => zero).toArray
  fun j => if j < 7 then av.getD j zero else zero

abbrev Mat := Array (Array F3P)

@[expose] def mget (A : Mat) (i j : ℕ) : F3P := (A.getD i #[]).getD j zero

@[expose] def elimMat (ρ : ℕ → F3P) : Mat :=
  let α := atomsF T ρ
  ((List.finRange 12).map fun i =>
    ((List.finRange 12).map fun j => (Elim.ent i j).evalM (mulT T) ρ α).toArray).toArray

@[expose] def luEntry (L U : Mat) (i j : ℕ) : F3P :=
  sumL ((List.range 12).map fun k => mulT T (mget L i k) (mget U k j))

@[expose] def luDecomp (A : Mat) : Mat × Mat := Id.run do
  let mut L : Mat := Array.replicate 12 (Array.replicate 12 zero)
  let mut U : Mat := Array.replicate 12 (Array.replicate 12 zero)
  for k in [0:12] do
    for j in [k:12] do
      let s := sumL ((List.range k).map fun t => mulT T (mget L k t) (mget U t j))
      U := U.modify k (·.set! j (sub (mget A k j) s))
    L := L.modify k (·.set! k one)
    let piv := invT T (mget U k k)
    for i in [k + 1:12] do
      let s := sumL ((List.range k).map fun t => mulT T (mget L i t) (mget U t k))
      L := L.modify i (·.set! k (mulT T (sub (mget A i k) s) piv))
  return (L, U)

@[expose] def luCheck (A L U : Mat) : Bool :=
  (List.range 12).all fun i => (List.range 12).all fun j =>
    (mget A i j == luEntry T L U i j) &&
    (if i = j then mget L i j == one else true) &&
    (if i < j then mget L i j == zero else true) &&
    (if j < i then mget U i j == zero else true)

@[expose] def normMat (A : Mat) : Mat := A.map (·.map normalize)

@[expose] def detAt (ρ : ℕ → F3P) : Option F3P :=
  let A := elimMat T ρ
  let LU := luDecomp T A
  let L := normMat LU.1
  let U := normMat LU.2
  if luCheck T A L U then some (prodT T ((List.range 12).map fun i => mget U i i)) else none

@[expose] def padd : List F3P → List F3P → List F3P
  | [], l => l
  | l, [] => l
  | a :: l, b :: l' => add a b :: padd l l'

@[expose] def pscale (c : F3P) (l : List F3P) : List F3P := l.map (mulT T c)

@[expose] def pmul : List F3P → List F3P → List F3P
  | [], _ => []
  | a :: l, l' => padd (pscale T a l') (zero :: pmul l l')

@[expose] def pneg (l : List F3P) : List F3P := l.map neg

@[expose] def ptrim (l : List F3P) : List F3P :=
  (l.reverse.dropWhile fun a => a.isZero).reverse

@[expose] def pdivmod (a b : List F3P) : List F3P × List F3P :=
  let b := ptrim b
  let db := b.length
  let lcInv := invT T (b.getLastD zero)
  let rec go : ℕ → List F3P → List F3P → List F3P × List F3P
    | 0, q, r => (q, r)
    | fuel + 1, q, r =>
      let r := ptrim r
      if r.length < db || db = 0 then (q, r) else
      let c := mulT T (r.getLastD zero) lcInv
      let sh := r.length - db
      go fuel (padd q (List.replicate sh zero ++ [c]))
        (padd r (pneg (List.replicate sh zero ++ pscale T c b)))
  go (a.length + 1) [] a

@[expose] def pxgcd (a b : List F3P) : List F3P × List F3P × List F3P :=
  let rec go : ℕ → List F3P → List F3P → List F3P → List F3P → List F3P → List F3P →
      List F3P × List F3P × List F3P
    | 0, r₀, _, s₀, _, t₀, _ => (r₀, s₀, t₀)
    | fuel + 1, r₀, r₁, s₀, s₁, t₀, t₁ =>
      if (ptrim r₁).isEmpty then (r₀, s₀, t₀) else
      let qr := pdivmod T r₀ r₁
      go fuel r₁ qr.2 s₁ (padd s₀ (pneg (pmul T qr.1 s₁))) t₁ (padd t₀ (pneg (pmul T qr.1 t₁)))
  go (a.length + b.length + 2) a b [one] [] [] [one]

@[expose] def interp (xs ys : List F3P) : List F3P := Id.run do
  let n := xs.length
  let xa := xs.toArray
  let mut c := ys.toArray
  for j in [1:n] do
    let mut i := n - 1
    while j ≤ i do
      let num := sub (c.getD i zero) (c.getD (i - 1) zero)
      let den := sub (xa.getD i zero) (xa.getD (i - j) zero)
      c := c.set! i (mulT T num (invT T den))
      if i = 0 then break
      i := i - 1
  let mut p : List F3P := []
  for k in [0:n] do
    let i := n - 1 - k
    p := padd (zero :: p) (pneg (pscale T (xa.getD i zero) p))
    p := padd p [c.getD i zero]
  return p

@[expose] def codePts (n : ℕ) : List F3P := (List.range n).map fun i => normalize (ofCode (i + 1))

@[expose] def vandProd (pts : List F3P) : F3P :=
  prodT T (pts ++ (pts.zipIdx.flatMap fun (x, i) => (pts.drop (i + 1)).map fun y => sub x y))

@[expose] def allSome : List (Option F3P) → Option (List F3P)
  | [] => some []
  | none :: _ => none
  | some a :: l => (allSome l).map (a :: ·)

@[expose] def zetaF (c0 c1 : F3P) : F3P := add one (mulT T c1 (mulT T c0 c0))

@[expose] def p1At (p' : List F3P) (ζ x xi : F3P) : F3P :=
  mulT T (PE.powM (mulT T) x (2 * D)) (horner T p' (mulT T ζ (mulT T xi xi)))

@[expose] def bezoutAt (p p' s t : List F3P) (ζ g x : F3P) : Bool :=
  let xi := normalize (invT T x)
  mulT T x xi == one &&
    add (mulT T (horner T s x) (horner T p x)) (mulT T (horner T t x) (p1At T p' ζ x xi)) == g

@[expose] def specCore (c0 c1 : F3P) (xs ys ys' : List F3P) : Bool :=
  let p := (interp T xs ys).map normalize
  let p' := (interp T xs ys').map normalize
  let ζ := zetaF T c0 c1
  let bpts := codePts (3 * D + 1)
  let p1 := (List.range (2 * D + 1)).map fun n =>
    if n % 2 = 0 then mulT T (p'.getD (D - n / 2) zero) (PE.powM (mulT T) ζ (D - n / 2))
    else zero
  let gst := pxgcd T p p1
  let s := (ptrim gst.2.1).map normalize
  let t := (ptrim gst.2.2).map normalize
  let g := normalize (gst.1.headD zero)
  p.length == D + 1 && p'.length ≤ D + 1 && s.length ≤ 2 * D && t.length ≤ D &&
    (List.zip xs ys).all (fun xy => horner T p xy.1 == xy.2) &&
    (List.zip xs ys').all (fun xy => horner T p' xy.1 == xy.2) &&
    unitT T (p.getD D zero) && unitT T (vandProd T xs) && unitT T (vandProd T bpts) &&
    unitT T g && bpts.all (bezoutAt T p p' s t ζ g)

@[expose] def specCheck (c0 c1 c2 c3 c4 : F3P) : Bool :=
  let c0 := normalize c0
  let c1 := normalize c1
  let c2 := normalize c2
  let c3 := normalize c3
  let c4 := normalize c4
  let xs := codePts (D + 1)
  match allSome (xs.map fun t => detAt T (ptVarsF c0 c1 c2 c3 t)),
    allSome (xs.map fun t => detAt T (ptVarsF c1 c2 c3 c4 t)) with
  | some ys, some ys' => specCore T c0 c1 xs ys ys'
  | _, _ => false

end

end Spec

end CFSG.Walter.Ree.Bombieri

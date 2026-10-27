module

public section

namespace Certificates.D5Twist

set_option compiler.extract_closed false

abbrev Mat := Array Nat

abbrev Vec := Array Nat

@[expose] def mulM (a b : Mat) : Mat :=
  Array.ofFn (n := 25) fun k =>
    let i := k.val / 5
    let j := k.val % 5
    (a[5 * i]! * b[j]! + a[5 * i + 1]! * b[5 + j]! + a[5 * i + 2]! * b[10 + j]! +
      a[5 * i + 3]! * b[15 + j]! + a[5 * i + 4]! * b[20 + j]!) % 3

@[expose] def mulV (a : Mat) (v : Vec) : Vec :=
  Array.ofFn (n := 5) fun i =>
    (a[5 * i.val]! * v[0]! + a[5 * i.val + 1]! * v[1]! + a[5 * i.val + 2]! * v[2]! +
      a[5 * i.val + 3]! * v[3]! + a[5 * i.val + 4]! * v[4]!) % 3

@[expose] def minusOneM : Mat :=
  #[2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2]

@[expose] def negM (a : Mat) : Mat := mulM minusOneM a

@[expose] def idM : Mat :=
  #[1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]

@[expose] def cart : Mat :=
  #[2, 2, 0, 0, 0, 2, 2, 2, 2, 0, 0, 2, 2, 0, 0, 0, 2, 0, 2, 2, 0, 0, 0, 2, 2]

@[expose] def sRefl (i : Nat) : Mat :=
  Array.ofFn (n := 25) fun k =>
    let p := k.val / 5
    let q := k.val % 5
    ((if p = q then 1 else 0) + 3 - (if p = i then cart[5 * i + q]! else 0)) % 3

@[expose] def xv : Vec := #[1, 2, 1, 2, 2]

@[expose] def twistM (gam : Array Nat) (lam c : Nat) : Mat :=
  Array.ofFn (n := 25) fun k =>
    let i := k.val / 5
    let j := k.val % 5
    if j < 4 then (if gam[j]! = i then c else 0)
    else
      (2 * lam * xv[i]! + 3 -
        (if i < 4 then (2 * c * xv[(gam.findIdx (· == i))]!) % 3 else 0)) % 3

@[expose] def invAux (g : Mat) : Nat → Mat → Mat → Mat
  | 0, _, prev => prev
  | n + 1, cur, prev => if cur == idM then prev else invAux g n (mulM g cur) cur

@[expose] def invM (g : Mat) : Mat := invAux g 1000 g idM

@[expose] def conjClosureAux (gens : List Mat) : Nat → List Mat → List Mat → List Mat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, r :: front, seen =>
    let new := (gens.map fun s => mulM (mulM s r) s).foldl
      (fun acc t => if seen.contains t || acc.contains t then acc else acc ++ [t]) []
    conjClosureAux gens n (front ++ new) (seen ++ new)

@[expose] def conjClosure (seed gens : List Mat) : List Mat := conjClosureAux gens 500 seed seed

@[expose] def simple5 (_ : Unit := ()) : List Mat := (List.range 5).map sRefl

@[expose] def S0 (_ : Unit := ()) : List Mat := conjClosure (simple5 ()) (simple5 ())

@[expose] def allVecs (_ : Unit := ()) : List Vec :=
  (List.range 243).map fun k =>
    #[k % 3, k / 3 % 3, k / 9 % 3, k / 27 % 3, k / 81 % 3]

@[expose] def fixedVecs (S : List Mat) : List Vec :=
  (allVecs ()).filter fun v => S.all fun s => mulV s v == v

@[expose] def lineOf (v : Vec) : Vec :=
  match v.toList.find? (· != 0) with
  | some t => v.map fun a => (a * t) % 3
  | none => v

@[expose] def zline (z : Vec) : List Vec := [#[0, 0, 0, 0, 0], z, z.map fun a => (2 * a) % 3]

@[expose] def wjGens (b : Nat) : List Mat := ((List.range 4).filter (· != b)).map sRefl

@[expose] def prodWord (gs : List Mat) (w : List Nat) : Mat :=
  w.foldl (fun acc i => mulM acc (gs[i]!)) idM

@[expose] def cG (gam : Array Nat) (lam c : Nat) : Mat := twistM gam lam c

@[expose] def cGi (gam : Array Nat) (lam c : Nat) : Mat := invM (cG gam lam c)

@[expose] def cRa (gam : Array Nat) (lam c : Nat) : Mat :=
  mulM (mulM (cG gam lam c) (sRefl 4)) (cGi gam lam c)

@[expose] def cGs (gam : Array Nat) (lam c : Nat) : List Mat := simple5 () ++ [cRa gam lam c]

@[expose] def cSp (gam : Array Nat) (lam c : Nat) : List Mat :=
  conjClosure (cGs gam lam c) (cGs gam lam c)

@[expose] def cWj (b : Nat) : List Mat := conjClosure (wjGens b) (wjGens b)

@[expose] def cLines (b : Nat) : List Vec :=
  (fixedVecs (cWj b)).filter fun z => z != #[0, 0, 0, 0, 0] && lineOf z == z

@[expose] def cRz (gam : Array Nat) (lam c : Nat) (z : Vec) : List Mat :=
  (cSp gam lam c).filter fun r => mulV r z == z

@[expose] def cOz (b : Nat) (gam : Array Nat) (lam c : Nat) (z : Vec) : List Mat :=
  conjClosure (cWj b) (cRz gam lam c z)

@[expose] def cLines15 (b : Nat) (gam : Array Nat) (lam c : Nat) : List Vec :=
  (cLines b).filter fun z => (cOz b gam lam c z).length == 15

@[expose] def cForced (b : Nat) (gam : Array Nat) (lam c : Nat) : List Mat :=
  (cLines15 b gam lam c).flatMap (cOz b gam lam c)

@[expose] def cCl (b : Nat) (gam : Array Nat) (lam c : Nat) : List Mat :=
  conjClosure (S0 () ++ cForced b gam lam c) (S0 () ++ cForced b gam lam c)

@[expose] def caseCheck (neg : Bool) (w : List Nat) (g gi : Mat) (gs sp wj : List Mat)
    (lines lines15 : List Vec) (oz : Vec → List Mat) (forced cl : List Mat) : Bool :=
  (mulM g gi == idM) &&
  (w.all fun i => i < 6) &&
  (prodWord gs w == (if neg then negM g else g)) &&
  (gs.all fun s => mulM s s == idM) &&
  (sp.all fun r => mulM r r == idM) &&
  (sp.all fun r => gs.all fun s => sp.contains (mulM (mulM s r) s)) &&
  (wj.length == 6) && (lines.length == 4) && (lines15.length == 2) &&
  (lines15.all fun z => lineOf z != xv) &&
  (lines15.all fun z => (fixedVecs (oz z)).all fun v => (zline z).contains v) &&
  (forced.all fun r => mulM r r == idM) &&
  (sp.all fun r => cl.contains r)

@[expose] def caseOk (b : Nat) (gam : Array Nat) (lam c : Nat) (neg : Bool) (w : List Nat) :
    Bool :=
  caseCheck neg w (cG gam lam c) (cGi gam lam c) (cGs gam lam c) (cSp gam lam c) (cWj b)
    (cLines b) (cLines15 b gam lam c) (cOz b gam lam c) (cForced b gam lam c) (cCl b gam lam c)

@[expose] def wordTable : List (Nat × Nat × Nat × Nat × Nat × Nat × Bool × List Nat) :=
  [
  (0, 2, 3, 0, 1, 1, false, [4, 3, 1, 0, 5, 2, 1, 3, 4, 0, 1, 3, 2, 1, 0, 5]),
  (0, 2, 3, 0, 1, 2, false, [4, 5, 0, 1, 3, 4, 2, 1, 0, 5, 3, 1, 2, 0, 1, 3, 4, 5, 4, 1]),
  (0, 2, 3, 0, 2, 1, true, [4, 5, 0, 1, 3, 4, 2, 1, 0, 5, 3, 1, 2, 0, 1, 3, 4, 5, 4, 1]),
  (0, 2, 3, 0, 2, 2, true, [4, 3, 1, 0, 5, 2, 1, 3, 4, 0, 1, 3, 2, 1, 0, 5]),
  (0, 3, 0, 2, 1, 1, false, [4, 3, 1, 2, 5, 0, 1, 3, 4, 2, 1, 3, 0, 1, 2, 5]),
  (0, 3, 0, 2, 1, 2, false, [4, 5, 2, 1, 3, 4, 0, 1, 2, 5, 3, 1, 2, 0, 1, 3, 4, 5, 4, 1]),
  (0, 3, 0, 2, 2, 1, true, [4, 5, 2, 1, 3, 4, 0, 1, 2, 5, 3, 1, 2, 0, 1, 3, 4, 5, 4, 1]),
  (0, 3, 0, 2, 2, 2, true, [4, 3, 1, 2, 5, 0, 1, 3, 4, 2, 1, 3, 0, 1, 2, 5]),
  (0, 3, 2, 0, 1, 1, true, [4, 3, 1, 0, 5, 2, 1, 3, 4, 0, 1, 3, 2, 1, 0, 5, 4, 3, 1, 2, 0, 1, 3, 4, 3, 1, 2, 0, 1, 3, 0, 1, 2, 0, 1, 0]),
  (0, 3, 2, 0, 1, 2, true, [4, 5, 3, 4, 0, 5, 3, 4, 3, 0]),
  (0, 3, 2, 0, 2, 1, false, [4, 5, 3, 4, 0, 5, 3, 4, 3, 0]),
  (0, 3, 2, 0, 2, 2, false, [4, 3, 1, 0, 5, 2, 1, 3, 4, 0, 1, 3, 2, 1, 0, 5, 4, 3, 1, 2, 0, 1, 3, 4, 3, 1, 2, 0, 1, 3, 0, 1, 2, 0, 1, 0]),
  (2, 0, 3, 2, 1, 1, true, [4, 3, 1, 2, 5, 0, 1, 3, 4, 2, 1, 3, 0, 1, 2, 5, 4, 3, 1, 2, 0, 1, 3, 4, 3, 1, 2, 0, 1, 3, 0, 1, 2, 0, 1, 0]),
  (2, 0, 3, 2, 1, 2, true, [4, 5, 3, 4, 2, 5, 3, 4, 3, 2]),
  (2, 0, 3, 2, 2, 1, false, [4, 5, 3, 4, 2, 5, 3, 4, 3, 2]),
  (2, 0, 3, 2, 2, 2, false, [4, 3, 1, 2, 5, 0, 1, 3, 4, 2, 1, 3, 0, 1, 2, 5, 4, 3, 1, 2, 0, 1, 3, 4, 3, 1, 2, 0, 1, 3, 0, 1, 2, 0, 1, 0]),
  (2, 2, 3, 0, 1, 1, false, [4, 3, 1, 0, 5, 2, 1, 3, 4, 0, 1, 3, 2, 1, 0, 5]),
  (2, 2, 3, 0, 1, 2, false, [4, 5, 0, 1, 3, 4, 2, 1, 0, 5, 3, 1, 2, 0, 1, 3, 4, 5, 4, 1]),
  (2, 2, 3, 0, 2, 1, true, [4, 5, 0, 1, 3, 4, 2, 1, 0, 5, 3, 1, 2, 0, 1, 3, 4, 5, 4, 1]),
  (2, 2, 3, 0, 2, 2, true, [4, 3, 1, 0, 5, 2, 1, 3, 4, 0, 1, 3, 2, 1, 0, 5]),
  (2, 3, 0, 2, 1, 1, false, [4, 3, 1, 2, 5, 0, 1, 3, 4, 2, 1, 3, 0, 1, 2, 5]),
  (2, 3, 0, 2, 1, 2, false, [4, 5, 2, 1, 3, 4, 0, 1, 2, 5, 3, 1, 2, 0, 1, 3, 4, 5, 4, 1]),
  (2, 3, 0, 2, 2, 1, true, [4, 5, 2, 1, 3, 4, 0, 1, 2, 5, 3, 1, 2, 0, 1, 3, 4, 5, 4, 1]),
  (2, 3, 0, 2, 2, 2, true, [4, 3, 1, 2, 5, 0, 1, 3, 4, 2, 1, 3, 0, 1, 2, 5]),
  (3, 0, 3, 2, 1, 1, true, [4, 3, 1, 2, 5, 0, 1, 3, 4, 2, 1, 3, 0, 1, 2, 5, 4, 3, 1, 2, 0, 1, 3, 4, 3, 1, 2, 0, 1, 3, 0, 1, 2, 0, 1, 0]),
  (3, 0, 3, 2, 1, 2, true, [4, 5, 3, 4, 2, 5, 3, 4, 3, 2]),
  (3, 0, 3, 2, 2, 1, false, [4, 5, 3, 4, 2, 5, 3, 4, 3, 2]),
  (3, 0, 3, 2, 2, 2, false, [4, 3, 1, 2, 5, 0, 1, 3, 4, 2, 1, 3, 0, 1, 2, 5, 4, 3, 1, 2, 0, 1, 3, 4, 3, 1, 2, 0, 1, 3, 0, 1, 2, 0, 1, 0]),
  (3, 2, 3, 0, 1, 1, false, [4, 3, 1, 0, 5, 2, 1, 3, 4, 0, 1, 3, 2, 1, 0, 5]),
  (3, 2, 3, 0, 1, 2, false, [4, 5, 0, 1, 3, 4, 2, 1, 0, 5, 3, 1, 2, 0, 1, 3, 4, 5, 4, 1]),
  (3, 2, 3, 0, 2, 1, true, [4, 5, 0, 1, 3, 4, 2, 1, 0, 5, 3, 1, 2, 0, 1, 3, 4, 5, 4, 1]),
  (3, 2, 3, 0, 2, 2, true, [4, 3, 1, 0, 5, 2, 1, 3, 4, 0, 1, 3, 2, 1, 0, 5]),
  (3, 3, 0, 2, 1, 1, false, [4, 3, 1, 2, 5, 0, 1, 3, 4, 2, 1, 3, 0, 1, 2, 5]),
  (3, 3, 0, 2, 1, 2, false, [4, 5, 2, 1, 3, 4, 0, 1, 2, 5, 3, 1, 2, 0, 1, 3, 4, 5, 4, 1]),
  (3, 3, 0, 2, 2, 1, true, [4, 5, 2, 1, 3, 4, 0, 1, 2, 5, 3, 1, 2, 0, 1, 3, 4, 5, 4, 1]),
  (3, 3, 0, 2, 2, 2, true, [4, 3, 1, 2, 5, 0, 1, 3, 4, 2, 1, 3, 0, 1, 2, 5]),
  (3, 3, 2, 0, 1, 1, true, [4, 3, 1, 0, 5, 2, 1, 3, 4, 0, 1, 3, 2, 1, 0, 5, 4, 3, 1, 2, 0, 1, 3, 4, 3, 1, 2, 0, 1, 3, 0, 1, 2, 0, 1, 0]),
  (3, 3, 2, 0, 1, 2, true, [4, 5, 3, 4, 0, 5, 3, 4, 3, 0]),
  (3, 3, 2, 0, 2, 1, false, [4, 5, 3, 4, 0, 5, 3, 4, 3, 0]),
  (3, 3, 2, 0, 2, 2, false, [4, 3, 1, 0, 5, 2, 1, 3, 4, 0, 1, 3, 2, 1, 0, 5, 4, 3, 1, 2, 0, 1, 3, 4, 3, 1, 2, 0, 1, 3, 0, 1, 2, 0, 1, 0])]

@[expose] def check (_ : Unit := ()) : Bool :=
  ((S0 ()).length == 20) && ((S0 ()).all fun r => mulM r r == idM) && (wordTable.length == 40) &&
  wordTable.all fun e =>
    caseOk e.1 #[e.2.1, 1, e.2.2.1, e.2.2.2.1] e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2

end Certificates.D5Twist

end

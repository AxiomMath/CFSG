module

public import CFSG.GH74.GLS.C3.Layer2.FinModelTabInputs

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

structure Dat where
  T : Nat
  I : Nat
  one : Nat
  x0 : Nat
  Q : Nat
  C : Nat
  Tr : List (List Nat)
  rel : List Nat
  L : List (List Nat)
  NM : List (List Nat)
  NL : List (List (List Nat))
  CM : Nat
  IV : Nat
  adm : List (Nat × Nat)
  adm7 : List (Nat × Nat)

@[expose] def g6 (T k : Nat) : Nat := (T >>> (6 * k)) % 64

@[expose] def bit (m k : Nat) : Bool := (m >>> k) % 2 == 1

@[expose] def f64 (x : Nat) : Fin 64 := ⟨x % 64, Nat.mod_lt _ (by decide)⟩

@[expose] def r64 : List Nat := List.range 64

@[expose] def gk (k : Nat) : Nat :=
  match k with
  | 0 => 6
  | 1 => 0
  | 2 => 2
  | _ => 8

@[expose] def tblOf (a : Nat) : Tbl := Vector.ofFn fun i => f64 (g6 a i)

variable (D : Dat)

@[expose] def mul (i j : Nat) : Nat := g6 D.T (64 * i + j)

@[expose] def cls3 (i : Nat) : Nat := bif i == D.one then 0 else bif mul D i i == D.one then 1 else 2

@[expose] def pairOK (x y gx gy : Nat) : Bool :=
  cls3 D (mul D x y) == cls3 D (mul D gx gy) && cls3 D (mul D y x) == cls3 D (mul D gy gx)

@[expose] def mkIdx (n : ℕ) [NeZero n] (g : Amb n) : Fin 64 :=
  ⟨((List.finRange 64).map fun i => keyA n ((mkTab n).el.get i)).idxOf (keyA n g) % 64,
    Nat.mod_lt _ (by decide)⟩

@[expose] def transOK (n : ℕ) [NeZero n] : Bool :=
  let t := mkTab n
  ((List.finRange 64).all fun i => (List.finRange 64).all fun j =>
    decide (t.el.get (f64 (mul D i j)) = t.el.get i * t.el.get j)) &&
  ((List.finRange 64).all fun k => mkIdx n (t.el.get k) == k) &&
  decide (t.el.get (f64 D.one) = 1) &&
  decide (t.el.get (f64 D.x0) = x0 n) &&
  ((List.finRange 64).all fun i => decide (t.el.get (f64 (g6 D.I i)) = (t.el.get i)⁻¹)) &&
  ((List.finRange 64).all fun i => t.isQ.get i == bit D.Q i) &&
  ((List.finRange 64).all fun i => t.cls.get i == g6 D.C i)

@[expose] def prs : List (Nat × Nat) := [(0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (2, 3)]

@[expose] def cm (i : Nat) : Nat := (D.CM >>> (64 * i)) % 2 ^ 64

@[expose] def dataOK : Bool :=
  D.one < 64 && D.x0 < 64 && mul D (gk 0) (gk 0) == D.x0 &&
  (D.rel.foldl (fun r k => mul D r (gk k)) D.one == D.one) &&
  (r64.all fun i => mul D D.one i == i) &&
  (D.Tr.foldl (fun (s : Option Nat) e =>
    match s, e with
    | some m, [i, p, k] =>
      bif i < 64 && !bit m i && bit m p && k < 4 && mul D p (gk k) == i then some (m ||| 1 <<< i)
      else none
    | _, _ => none) (some (1 <<< D.one))) == some (2 ^ 64 - 1) &&
  ((List.range 4).all fun k => D.L.getD k [] == r64.filter fun h => cls3 D h == cls3 D (gk k)) &&
  ((List.range 6).all fun q =>
    let (k, l) := prs.getD q (0, 0)
    let M := D.NM.getD q []
    let N := D.NL.getD q []
    M.length == 64 && N.length == 64 &&
    r64.all fun x =>
      let m := M.getD x 0
      m < 2 ^ 64 && N.getD x [] == r64.filter (bit m) &&
      r64.all fun y => bit m y == (cls3 D y == cls3 D (gk l) && pairOK D x y (gk k) (gk l))) &&
  (r64.all fun i =>
    bit D.IV i == (i != D.one && mul D i i == D.one) &&
    r64.all fun j => bit (cm D i) j ==
      (bit D.IV i && bit D.IV j && g6 D.C i == g6 D.C j))

@[expose] def hk (h0 h1 h2 h3 k : Nat) : Nat :=
  match k with
  | 0 => h0
  | 1 => h1
  | 2 => h2
  | _ => h3

@[expose] def ofImg (h0 h1 h2 h3 : Nat) : Nat :=
  D.Tr.foldl (fun acc e =>
    match e with
    | [i, p, k] => acc ||| mul D (g6 acc p) (hk h0 h1 h2 h3 k) <<< (6 * i)
    | _ => acc) (D.one <<< (6 * D.one))

@[expose] def stepK (a S : Nat) : Nat :=
  r64.foldl (fun acc i =>
    bif bit S i && bit D.IV i then
      (let j := g6 a i; acc ||| cm D i ||| (bif bit D.IV j then 1 <<< j else 0))
    else acc) S

@[expose] def reachK (a : Nat) : Nat → Nat → Nat
  | 0, S => S
  | f + 1, S => let S' := stepK D a S; bif S' == S then S else reachK a f S'

@[expose] def sqAt (a u i : Nat) : Bool := g6 a (g6 a i) == mul D (mul D u i) (g6 D.I u)

@[expose] def pairsOf (a : Nat) : List (Nat × Nat) :=
  let us := r64.filter fun u =>
    g6 a u == u && ((List.range 4).all fun k => sqAt D a u (gk k)) && r64.all (sqAt D a u)
  match us with
  | [] => []
  | _ =>
    let X0 := reachK D a 12 (1 <<< D.x0)
    let V0 := reachK D a 12 (1 <<< mul D D.x0 (g6 a D.x0))
    bif X0 &&& V0 == 0 && ((V0 &&& D.Q) ||| 1 <<< D.one) == 1 <<< D.one then us.map (a, ·) else []

@[expose] def leaf (h0 h1 h2 h3 : Nat) : List (Nat × Nat) :=
  bif D.rel.foldl (fun r k => mul D r (hk h0 h1 h2 h3 k)) D.one == D.one then
    (let a := ofImg D h0 h1 h2 h3
     bif g6 a D.x0 != D.x0 then pairsOf D a else [])
  else []

@[expose] def search : List (Nat × Nat) :=
  let NM := fun q x => (D.NM.getD q []).getD x 0
  let NL := fun q x => (D.NL.getD q []).getD x []
  (D.L.getD 0 []).flatMap fun h0 =>
    bif mul D h0 h0 == D.x0 then [] else
    (NL 0 h0).flatMap fun h1 =>
      let m2 := NM 1 h0
      let m3 := NM 3 h0 &&& NM 4 h1
      (NL 2 h1).flatMap fun h2 =>
        bif bit m2 h2 then
          (NL 5 h2).flatMap fun h3 => bif bit m3 h3 then leaf D h0 h1 h2 h3 else []
        else []

@[expose] def searchOK : Bool := search D == D.adm

@[expose] def autOK (a : Nat) : Bool :=
  g6 a D.one == D.one &&
  (r64.all fun i => (List.range 4).all fun k =>
    g6 a (mul D i (gk k)) == mul D (g6 a i) (g6 a (gk k))) &&
  r64.all fun i => !(g6 a i == D.one) || i == D.one

@[expose] def admAutOK : Bool := D.adm.all fun p => autOK D p.1

end CFSG.KC.GH74Tab

end

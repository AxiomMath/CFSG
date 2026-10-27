module

public section

namespace CFSG.Quasithin.B45Exc.L33

structure M3 where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  g : Nat
  h : Nat
  i : Nat
deriving DecidableEq

namespace M3

@[expose] def mul (x y : M3) : M3 :=
  ⟨(x.a * y.a + x.b * y.d + x.c * y.g) % 3, (x.a * y.b + x.b * y.e + x.c * y.h) % 3,
    (x.a * y.c + x.b * y.f + x.c * y.i) % 3,
   (x.d * y.a + x.e * y.d + x.f * y.g) % 3, (x.d * y.b + x.e * y.e + x.f * y.h) % 3,
    (x.d * y.c + x.e * y.f + x.f * y.i) % 3,
   (x.g * y.a + x.h * y.d + x.i * y.g) % 3, (x.g * y.b + x.h * y.e + x.i * y.h) % 3,
    (x.g * y.c + x.h * y.f + x.i * y.i) % 3⟩

@[expose] def one : M3 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

@[expose] def negOne : M3 := ⟨2, 0, 0, 0, 2, 0, 0, 0, 2⟩

@[expose] def tr (x : M3) : M3 := ⟨x.a, x.d, x.g, x.b, x.e, x.h, x.c, x.f, x.i⟩

@[expose] def det (x : M3) : Nat :=
  (x.a * ((x.e * x.i + 2 * (x.f * x.h)) % 3) + 2 * (x.b * ((x.d * x.i + 2 * (x.f * x.g)) % 3)) +
    x.c * ((x.d * x.h + 2 * (x.e * x.g)) % 3)) % 3

@[expose] def adj (x : M3) : M3 :=
  ⟨(x.e * x.i + 2 * (x.f * x.h)) % 3, (x.c * x.h + 2 * (x.b * x.i)) % 3,
    (x.b * x.f + 2 * (x.c * x.e)) % 3,
   (x.f * x.g + 2 * (x.d * x.i)) % 3, (x.a * x.i + 2 * (x.c * x.g)) % 3,
    (x.c * x.d + 2 * (x.a * x.f)) % 3,
   (x.d * x.h + 2 * (x.e * x.g)) % 3, (x.b * x.g + 2 * (x.a * x.h)) % 3,
    (x.a * x.e + 2 * (x.b * x.d)) % 3⟩

@[expose] def pow (x : M3) : Nat → M3
  | 0 => one
  | n + 1 => mul (pow x n) x

@[expose] def vals : List Nat := List.range 3

@[expose] def all : List M3 :=
  vals.flatMap fun a => vals.flatMap fun b => vals.flatMap fun c =>
  vals.flatMap fun d => vals.flatMap fun e => vals.flatMap fun f =>
  vals.flatMap fun g => vals.flatMap fun h => vals.map fun i => ⟨a, b, c, d, e, f, g, h, i⟩

@[expose] def sl3 : List M3 := all.filter fun x => x.det == 1

@[expose] def invs : List M3 := sl3.filter fun x => mul x x == one && x != one

@[expose] def syms : List M3 := all.filter fun A => tr A == A && A.det != 0

@[expose] def ord13 (y : M3) : Bool := pow y 13 == one && y != one

@[expose] def so (B : M3) : List M3 := sl3.filter fun x => mul x (mul B (tr x)) == B

@[expose] def isSO (B x : M3) : Bool := x.det == 1 && mul x (mul B (tr x)) == B

@[expose] def conj (t x : M3) : M3 := mul x (mul t (adj x))

@[expose] def checkC1 : Bool :=
  syms.all fun A => sl3.any fun y => mul y A == mul A (tr y) && ord13 y

@[expose] def checkC2 : Bool :=
  invs.all fun t =>
    let Ct := sl3.filter fun g => mul g t == mul t g
    invs.all fun u => !(t != u && mul t u == mul u t) ||
      Ct.any fun g => mul g (adj g) == one &&
        (let w := mul u (mul g (mul u (adj g)))
         pow w 4 == one && pow w 2 != one)

@[expose] def witI (t u : M3) : Option (M3 × M3 × M3) :=
  let S2 := so t
  let S3 := so u
  (so one).findSome? fun x1 =>
    let p := conj t x1
    S2.findSome? fun x2 =>
      let q := mul p (conj t x2)
      S3.findSome? fun x3 => if ord13 (mul q (conj t x3)) then some (x1, x2, x3) else none

@[expose] def tabI : List ((M3 × M3) × (M3 × M3 × M3)) :=
  let invI := (so one).filter fun t => mul t t == one && t != one
  invI.flatMap fun t => invI.filterMap fun u =>
    if t != u && mul t u == mul u t then (witI t u).map fun w => ((t, u), w) else none

@[expose] def findP (A : M3) : Option M3 :=
  sl3.find? fun P => let Q := mul P (mul A (tr P)); Q == one || Q == negOne

@[expose] def pTab : List (M3 × M3) := syms.filterMap fun A => (findP A).map fun P => (A, P)

@[expose] def cands (oP : Option M3) (t u : M3) : List (M3 × M3 × M3) :=
  match oP with
  | none => []
  | some P =>
    let Pi := adj P
    match (tabI.find? fun e => e.1 == (conj t P, conj u P)) with
    | none => []
    | some e => [(mul Pi (mul e.2.1 P), mul Pi (mul e.2.2.1 P), mul Pi (mul e.2.2.2 P))]

@[expose] def good (A t u : M3) (w : M3 × M3 × M3) : Bool :=
  isSO A w.1 && isSO (mul t A) w.2.1 && isSO (mul u A) w.2.2 &&
    mul w.1 (adj w.1) == one && mul w.2.1 (adj w.2.1) == one && mul w.2.2 (adj w.2.2) == one &&
    ord13 (mul (mul (conj t w.1) (conj t w.2.1)) (conj t w.2.2))

@[expose] def checkC3 : Bool :=
  invs.all fun t =>
    let Ct := invs.filter fun u => t != u && mul t u == mul u t
    syms.all fun A => !(isSO A t) ||
      (let oP := (pTab.find? fun e => e.1 == A).map Prod.snd
       Ct.all fun u => !(isSO A u) || (cands oP t u).any (good A t u))

end M3

end CFSG.Quasithin.B45Exc.L33

module

public import Certificates.Data.SmithB45ExcL33

public section

namespace CFSG.KC.B45L33

open CFSG.Quasithin.B45Exc.L33 CFSG.Quasithin.B45Exc.L33.M3

@[expose] def eqM (x y : M3) : Bool :=
  x.a == y.a && x.b == y.b && x.c == y.c && x.d == y.d && x.e == y.e && x.f == y.f &&
    x.g == y.g && x.h == y.h && x.i == y.i

@[expose] def eqL : List M3 → List M3 → Bool
  | [], [] => true
  | x :: l, y :: l' => eqM x y && eqL l l'
  | _, _ => false

@[expose] def eqL2 : List (M3 × M3) → List (M3 × M3) → Bool
  | [], [] => true
  | x :: l, y :: l' => eqM x.1 y.1 && eqM x.2 y.2 && eqL2 l l'
  | _, _ => false

@[expose] def isSOK (B x : M3) : Bool := x.det == 1 && eqM (mul x (mul B (tr x))) B

@[expose] def ord13K (y : M3) : Bool := eqM (pow y 13) one && !eqM y one

@[expose] def goodK (A t u : M3) (w : M3 × M3 × M3) : Bool :=
  isSOK A w.1 && isSOK (mul t A) w.2.1 && isSOK (mul u A) w.2.2 &&
    eqM (mul w.1 (adj w.1)) one && eqM (mul w.2.1 (adj w.2.1)) one &&
    eqM (mul w.2.2 (adj w.2.2)) one &&
    ord13K (mul (mul (conj t w.1) (conj t w.2.1)) (conj t w.2.2))

@[expose] def invEnum : List M3 :=
  vals.flatMap fun a => vals.flatMap fun b => vals.flatMap fun c =>
  vals.flatMap fun d => vals.flatMap fun g =>
  if (a * a + b * d + c * g) % 3 == 1 then
    vals.flatMap fun e => vals.flatMap fun h =>
    if (a * b + b * e + c * h) % 3 == 0 then
      vals.flatMap fun f =>
      if (d * a + e * d + f * g) % 3 == 0 && (d * b + e * e + f * h) % 3 == 1 then
        (vals.map fun i => (⟨a, b, c, d, e, f, g, h, i⟩ : M3)).filter fun x =>
          x.det == 1 && eqM (mul x x) one && !eqM x one
      else []
    else []
  else []

@[expose] def symInv : List M3 :=
  (vals.flatMap fun a => vals.flatMap fun b => vals.flatMap fun c =>
   vals.flatMap fun e => vals.flatMap fun f => vals.map fun i =>
     (⟨a, b, c, b, e, f, c, f, i⟩ : M3)).filter fun A => A.det != 0

@[expose] def pairsEnum (I : List M3) : List (M3 × M3) :=
  I.flatMap fun t => (I.filter fun u => !eqM t u && eqM (mul t u) (mul u t)).map fun u => (t, u)

@[expose] def invOK (I : List M3) : Bool := eqL invEnum I

@[expose] def c1ok (A y P : M3) : Bool :=
  y.det == 1 && eqM (mul y A) (mul A (tr y)) && eqM (pow y 13) one && !eqM (mul one y) one &&
    P.det == 1 && eqM (mul P (adj P)) one && eqM (mul (adj P) P) one &&
    (eqM (mul P (mul A (tr P))) one || eqM (mul P (mul A (tr P))) negOne)

@[expose] def symOK (S : List (M3 × M3 × M3)) : Bool :=
  eqL symInv (S.map Prod.fst) && S.all fun e => c1ok e.1 e.2.1 e.2.2

@[expose] def c2ok (t u g : M3) : Bool :=
  g.det == 1 && eqM (mul g t) (mul t g) && eqM (mul g (adj g)) one &&
    (let w := mul u (mul g (mul u (adj g)))
     eqM (pow w 4) one && !eqM (pow w 2) one)

@[expose] def pairsOK (I : List M3) (Pr : List (M3 × M3 × M3)) : Bool :=
  eqL2 (pairsEnum I) (Pr.map fun e => (e.1, e.2.1)) && Pr.all fun e => c2ok e.1 e.2.1 e.2.2

@[expose] def c3OK (Pr : List (M3 × M3 × M3)) (W : List ((M3 × M3) × (M3 × M3 × M3))) : Bool :=
  Pr.all fun e => !(isSOK one e.1 && isSOK one e.2.1) ||
    W.any fun w => eqM w.1.1 e.1 && eqM w.1.2 e.2.1 && goodK one e.1 e.2.1 w.2

end CFSG.KC.B45L33

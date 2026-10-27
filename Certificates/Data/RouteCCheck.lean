module

public section

namespace CFSG.CGT.PushingUpLit.CGT6.RouteC

abbrev Mat := List Nat

@[expose] def mulVec : Mat → Nat → Nat
  | [], _ => 0
  | a :: as, v => (if v % 2 = 1 then a else 0) ^^^ mulVec as (v / 2)

@[expose] def mul (A B : Mat) : Mat := B.map (mulVec A)

@[expose] def one : Mat := [1, 2, 4, 8, 16, 32]

@[expose] def add (A B : Mat) : Mat := List.zipWith (· ^^^ ·) A B

@[expose] def pow (A : Mat) : Nat → Mat
  | 0 => one
  | k + 1 => mul A (pow A k)

@[expose] def spanList : List Nat → List Nat
  | [] => [0]
  | b :: bs => spanList bs ++ (spanList bs).map (· ^^^ b)

@[expose] def chartY (φ : Nat) : Mat :=
  [2, 3, φ % 4 + 4, φ / 4 % 4 + 8, φ % 4 + 16, φ / 4 % 4 + 32]

@[expose] def chartD (ψ : Nat) : Mat :=
  [1 + 4 * (ψ % 2) + 8 * (ψ / 2 % 2), 2 + 4 * (ψ / 4 % 2) + 8 * (ψ / 8 % 2), 8, 12,
    16 + 4 * (ψ / 16 % 2) + 8 * (ψ / 32 % 2), 32 + 4 * (ψ / 64 % 2) + 8 * (ψ / 128 % 2)]

@[expose] def chartT : Mat := [1, 2, 16, 32, 4, 8]

@[expose] def gen (φ ψ : Nat) : Nat → Mat
  | 0 => chartY φ
  | 1 => chartD ψ
  | 2 => chartT
  | 3 => mul (chartY φ) (chartY φ)
  | _ => mul (chartD ψ) (chartD ψ)

@[expose] def evalW (φ ψ : Nat) (w : List Nat) : Mat :=
  w.foldl (fun acc l => mul acc (gen φ ψ l)) one

@[expose] def invL (l : Nat) : Nat :=
  if l = 0 then 3 else if l = 3 then 0 else if l = 1 then 4 else if l = 4 then 1 else l

@[expose] def invW (w : List Nat) : List Nat := w.reverse.map invL

@[expose] def eqMod (Kels : List Nat) (A B : Mat) : Bool :=
  (add A B).all fun x => Kels.contains x

@[expose] def invariantUnder (Kb Kels : List Nat) (A : Mat) : Bool :=
  Kb.all fun b => Kels.contains (mulVec A b)

@[expose] def kOk (Kels : List Nat) : Bool := [1, 2, 3, 4, 8, 12].all fun x => !Kels.contains x

@[expose] def condT (Kb Kels : List Nat) : Bool :=
  invariantUnder Kb Kels chartT && kOk Kels && (add chartT one).any fun x => !Kels.contains x

@[expose] def condY (Kb Kels : List Nat) (φ : Nat) : Bool := invariantUnder Kb Kels (chartY φ)

@[expose] def condD (Kb Kels : List Nat) (ψ : Nat) : Bool := invariantUnder Kb Kels (chartD ψ)

@[expose] def kList : Nat → List (List Nat)
  | 0 => [[]]
  | 1 => (List.range 64).filterMap fun v => if v ≠ 0 then some [v] else none
  | 2 => (List.range 64).flatMap fun a => (List.range 64).filterMap fun b =>
      if 0 < a ∧ a < b then some [a, b] else none
  | _ => []

@[expose] def members (n : Nat) : List (List Nat × Nat × Nat) :=
  (kList (6 - n)).flatMap fun Kb =>
    if condT Kb (spanList Kb) then
      ((List.range 16).filter (condY Kb (spanList Kb))).flatMap fun φ =>
        ((List.range 256).filter (condD Kb (spanList Kb))).map fun ψ => (Kb, φ, ψ)
    else []

@[expose] def addVec (basis : List Nat) (v : Nat) : List Nat :=
  if (spanList basis).contains v then basis else v :: basis

@[expose] def closeStep (gens : List Mat) (basis : List Nat) : List Nat :=
  (gens.flatMap fun g => basis.map (mulVec g)).foldl addVec basis

@[expose] def closeBasis (gens : List Mat) (start : List Nat) : List Nat :=
  (List.range 7).foldl (fun b _ => closeStep gens b) (start.foldl addVec [])

@[expose] def checkB (φ ψ : Nat) (Kb : List Nat) (m : Nat) (g : List Nat) : Bool :=
  let Kels := spanList Kb
  let gens := [chartY φ, chartD ψ, chartT]
  let km1 := add (pow (evalW φ ψ g) m) one
  let Wb := closeBasis gens (Kb ++ km1)
  (Wb.all fun b => gens.all fun g => (spanList Wb).contains (mulVec g b)) &&
  (km1.all fun x => (spanList Wb).contains x) &&
  (Wb.all fun b => Kels.contains (mulVec km1 b)) &&
  (km1.any fun x => !Kels.contains x)

@[expose] def checkC (φ ψ : Nat) (Kels : List Nat) (a m : Nat) (cw : List Nat) : Bool :=
  let ct := evalW φ ψ cw
  let ci := evalW φ ψ (invW cw)
  let x := mul (chartY φ) (mul ct (mul (chartY φ) ci))
  eqMod Kels (mul chartT ct) (mul ct chartT) &&
  eqMod Kels (mul ct ci) one &&
  m % 3 != 0 &&
  !eqMod Kels (pow x a) one &&
  eqMod Kels (pow (pow x a) m) one

@[expose] def checkS (n φ ψ : Nat) (Kels : List Nat) (s : Mat × Mat × Mat) (θ : Mat) : Bool :=
  θ.length == 6 && θ.all (· < 2 ^ n) &&
  (chartY φ).map (mulVec θ) == θ.map (mulVec s.1) &&
  (chartD ψ).map (mulVec θ) == θ.map (mulVec s.2.1) &&
  chartT.map (mulVec θ) == θ.map (mulVec s.2.2) &&
  (List.range 64).all (fun x => (mulVec θ x == 0) == Kels.contains x) &&
  (List.range (2 ^ n)).all fun v => (spanList θ).contains v

@[expose] def memberOk (surv : List (Mat × Mat × Mat)) (n : Nat) (Kb : List Nat) (φ ψ : Nat)
    (w : List Nat) : Bool :=
  match w with
  | 0 :: m :: g => checkB φ ψ Kb m g
  | 1 :: a :: m :: cw => checkC φ ψ (spanList Kb) a m cw
  | 3 :: i :: θ =>
    match surv[i]? with
    | some s => checkS n φ ψ (spanList Kb) s θ
    | none => false
  | _ => false

@[expose] def unpack : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, x => if x = 0 then [] else (x % 100 - 1) :: unpack fuel (x / 100)

@[expose] def check (surv : List (Mat × Mat × Mat)) (n : Nat) (data : List Nat) : Bool :=
  (members n).length == data.length &&
    (List.zipWith (fun m x => memberOk surv n m.1 m.2.1 m.2.2 (unpack 64 x)) (members n) data).all
      id

end CFSG.CGT.PushingUpLit.CGT6.RouteC

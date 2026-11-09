module

public import Certificates.Data.Kernel.Cert690.Sq

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

@[expose] noncomputable def fB (g n : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun _ ih v => if v = 0 then false else
      (ih (v ^^^ (1 <<< lowIdx v)) ^^
        b0n (Code.act g (v ^^^ (1 <<< lowIdx v))) (Code.act g (1 <<< lowIdx v)) ^^
        b0n (v ^^^ (1 <<< lowIdx v)) (1 <<< lowIdx v))) n

@[expose] def dotN (f v : ℕ) : Bool :=
  (f.testBit 0 && v.testBit 0) ^^ (f.testBit 1 && v.testBit 1) ^^ (f.testBit 2 && v.testBit 2) ^^
    (f.testBit 3 && v.testBit 3) ^^ (f.testBit 4 && v.testBit 4) ^^ (f.testBit 5 && v.testBit 5)

@[expose] noncomputable def liftF (g f x : ℕ) : ℕ :=
  (x % 2 ^^^ (if (fB g 64 (x / 2) ^^ dotN f (x / 2)) then 1 else 0)) + 2 * Code.act g (x / 2)

@[expose] noncomputable def invF (g g' f y : ℕ) : ℕ :=
  (y % 2 ^^^ (if (fB g 64 (Code.act g' (y / 2)) ^^ dotN f (Code.act g' (y / 2))) then 1 else 0)) +
    2 * Code.act g' (y / 2)

@[expose] def innWF (φ : ℕ → ℕ) : ℕ :=
  2 * (φ 2 % 2) + φ 4 % 2 + 8 * (φ 8 % 2) + 4 * (φ 16 % 2) + 32 * (φ 32 % 2) + 16 * (φ 64 % 2)

@[expose] def guessF (φ : ℕ → ℕ) : Option ℕ :=
  if (List.range 128).all (fun x => qmulN (qmulN (qinvN (2 * innWF φ)) x) (2 * innWF φ) == φ x)
  then some (2 * innWF φ) else none

@[expose] def qGens : List ℕ := [0, 1, 2, 4, 8, 16, 32, 64]

@[expose] def guessG (φ : ℕ → ℕ) : Option ℕ :=
  if qGens.all (fun x => qmulN (qmulN (qinvN (2 * innWF φ)) x) (2 * innWF φ) == φ x)
  then some (2 * innWF φ) else none

@[expose] noncomputable def rootF (r : ℕ) : ℕ := 2 * innWF fun x => liftF r 0 (liftF r 0 x)

@[expose] noncomputable def candOneT (f : ℕ) : Option ℕ :=
  match guessF (liftF Code.one f) with
  | some e => if e < 128 then some (qmulN e e) else none
  | none => none

@[expose] noncomputable def candT (r₁ r₂ : ℕ) (w : ℕ × ℕ × ℕ × ℕ) (f : ℕ) (b : Bool × Bool) :
    Option ℕ :=
  match guessF (fun x => liftF w.1 f (liftF w.2.2.1 0 (invF (if w.2.1 = 0 then r₁ else r₂)
      (if w.2.1 = 0 then r₁ else r₂) 0 (invF w.2.2.1 w.2.2.2 0 x)))) with
  | some e =>
    if e < 128 then
      some (qmulN (qmulN (liftF w.2.2.1 0 (sOf #[rootF r₁, rootF r₂] b.1 b.2 w.2.1))
        (liftF w.2.2.1 0 (liftF (if w.2.1 = 0 then r₁ else r₂) 0 (invF w.2.2.1 w.2.2.2 0 e)))) e)
    else none
  | none => none

@[expose] def evensF : List ℕ := (List.range 64).filter fun f => !f.testBit 0

@[expose] noncomputable def valsT (r₁ r₂ : ℕ) (Ws : List (ℕ × ℕ × ℕ × ℕ)) (b : Bool × Bool) :
    List (Option ℕ) :=
  evensF.map candOneT ++ Ws.flatMap fun w => evensF.map fun f => candT r₁ r₂ w f b

@[expose] noncomputable def candOneA8G (f : ℕ) : Option ℕ :=
  match guessG (liftF Code.one f) with
  | some e => if e < 128 then some (qmulN e e) else none
  | none => none

@[expose] noncomputable def candA8G (r₁ r₂ : ℕ) (w : ℕ × ℕ × ℕ × ℕ) (f : ℕ) (b : Bool × Bool) :
    Option ℕ :=
  match guessG (fun x => liftF w.1 f (liftF w.2.2.1 0 (invF (if w.2.1 = 0 then r₁ else r₂)
      (if w.2.1 = 0 then r₁ else r₂) 0 (invF w.2.2.1 w.2.2.2 0 x)))) with
  | some e =>
    if e < 128 then
      some (qmulN (qmulN (liftF w.2.2.1 0 (sOf #[rootF r₁, rootF r₂] b.1 b.2 w.2.1))
        (liftF w.2.2.1 0 (liftF (if w.2.1 = 0 then r₁ else r₂) 0 (invF w.2.2.1 w.2.2.2 0 e)))) e)
    else none
  | none => none

@[expose] noncomputable def valsA8G (r₁ r₂ : ℕ) (Ws : List (ℕ × ℕ × ℕ × ℕ)) (b : Bool × Bool) :
    List (Option ℕ) :=
  evensF.map candOneA8G ++ Ws.flatMap fun w => evensF.map fun f => candA8G r₁ r₂ w f b

@[expose] def qWord (x : ℕ) : List ℕ :=
  let l := ((List.range 6).filter fun j => (x / 2).testBit j).map fun j => 2 ^ (j + 1)
  if l.foldl qmulN 0 == x then l else l ++ [1]

@[expose] def qWordF (Y : ℕ → ℕ) (e : ℕ) : ℕ := (qWord e).foldl (fun a g => qmulN a (Y g)) (Y 0)

@[expose] noncomputable def candA8Y (r₁ r₂ : ℕ) (w : ℕ × ℕ × ℕ × ℕ) (f : ℕ) (b : Bool × Bool) :
    Option ℕ :=
  match guessG (fun x => liftF w.1 f (liftF w.2.2.1 0 (invF (if w.2.1 = 0 then r₁ else r₂)
      (if w.2.1 = 0 then r₁ else r₂) 0 (invF w.2.2.1 w.2.2.2 0 x)))) with
  | some e =>
    if e < 128 then
      some (qmulN (qmulN (liftF w.2.2.1 0 (sOf #[rootF r₁, rootF r₂] b.1 b.2 w.2.1))
        (qWordF (fun y => liftF w.2.2.1 0 (liftF (if w.2.1 = 0 then r₁ else r₂) 0
          (invF w.2.2.1 w.2.2.2 0 y))) e)) e)
    else none
  | none => none

@[expose] noncomputable def valsA8Y (r₁ r₂ : ℕ) (Ws : List (ℕ × ℕ × ℕ × ℕ)) (b : Bool × Bool) :
    List (Option ℕ) :=
  evensF.map candOneA8G ++ Ws.flatMap fun w => evensF.map fun f => candA8Y r₁ r₂ w f b

@[expose] def zFlipA8 (x : ℕ) : ℕ := (x % 2 ^^^ 1) + 2 * (x / 2)

@[expose] def bitA8 (w : ℕ × ℕ × ℕ × ℕ) (b : Bool × Bool) : Bool := if w.2.1 == 0 then b.1 else b.2

@[expose] noncomputable def valsA8Z (r₁ r₂ : ℕ) (Ws : List (ℕ × ℕ × ℕ × ℕ)) (b : Bool × Bool) :
    List (Option ℕ) :=
  evensF.map candOneA8G ++ Ws.flatMap fun w => evensF.map fun f =>
    (candA8Y r₁ r₂ w f (false, false)).map fun v => if bitA8 w b then zFlipA8 v else v

@[expose] def tailL (l : List (Option ℕ)) : Bool :=
  l.all (fun o => o.isSome) && l.length == (l.filterMap fun o => o).length &&
    ((l.filterMap fun o => o).filter fun x => x == a0N).length == 120 &&
    [72, 336, 408, 672].contains ((l.filterMap fun o => o).filter fun x => x == z0N).length

@[expose] def stepA8 (o : Option ℕ) (acc : Option (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  match o, acc with
  | some x, some p => some (p.1 + (if x == a0N then 1 else 0), p.2 + (if x == z0N then 1 else 0))
  | _, _ => none

@[expose] def cntA8 (l : List (Option ℕ)) : Option (ℕ × ℕ) := l.foldr stepA8 (some (0, 0))

@[expose] def tailA8 (l : List (Option ℕ)) : Bool :=
  match cntA8 l with
  | some p => p.1 == 120 && [72, 336, 408, 672].contains p.2
  | none => false

@[expose] noncomputable def tagA8 (r₁ r₂ : ℕ) (Ws : List (ℕ × ℕ × ℕ × ℕ)) : List (ℕ × Option ℕ) :=
  evensF.map (fun f => (0, candOneA8G f)) ++ Ws.flatMap fun w => evensF.map fun f =>
    (if w.2.1 == 0 then 1 else 2, candA8Y r₁ r₂ w f (false, false))

@[expose] def add4A8 (c : ℕ × ℕ × ℕ × ℕ) (v : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (c.1 + (if v == 0 then 1 else 0), c.2.1 + (if v == 1 then 1 else 0),
    c.2.2.1 + (if v == 2 then 1 else 0), c.2.2.2 + (if v == 3 then 1 else 0))

@[expose] def step12A8 (e : ℕ × Option ℕ)
    (acc : Option ((ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ))) :
    Option ((ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) :=
  match e.2, acc with
  | some v, some s => some (if e.1 == 0 then (add4A8 s.1 v, s.2) else if e.1 == 1 then
      (s.1, add4A8 s.2.1 v, s.2.2) else (s.1, s.2.1, add4A8 s.2.2 v))
  | _, _ => none

@[expose] def cnt12A8 (T : List (ℕ × Option ℕ)) :
    Option ((ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) :=
  T.foldr step12A8 (some ((0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0)))

@[expose] def dec4A8 (t : Bool) (c : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ :=
  if t then (c.2.2.2, c.1) else (c.2.2.1, c.2.1)

@[expose] def decTA8 (b : Bool × Bool)
    (s : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) : ℕ × ℕ :=
  ((dec4A8 false s.1).1 + (dec4A8 b.1 s.2.1).1 + (dec4A8 b.2 s.2.2).1,
    (dec4A8 false s.1).2 + (dec4A8 b.1 s.2.1).2 + (dec4A8 b.2 s.2.2).2)

@[expose] noncomputable def fuseA8 (r₁ r₂ : ℕ) (Ws : List (ℕ × ℕ × ℕ × ℕ)) : Bool :=
  match cnt12A8 (tagA8 r₁ r₂ Ws) with
  | some s => certBits.all fun b => (decTA8 b s).1 == 120 && [72, 336, 408, 672].contains (decTA8 b s).2
  | none => false

@[expose] def invPair (g g' : ℕ) : Bool :=
  (List.range 64).all fun u => Code.act g (Code.act g' u) == u && Code.act g' (Code.act g u) == u

@[expose] def invPairM (g g' : ℕ) : Bool := Code.mul g g' == Code.one && Code.mul g' g == Code.one

@[expose] noncomputable def a8T (r₁ r₂ : ℕ) (Ws : List (ℕ × ℕ × ℕ × ℕ)) : Bool :=
  invPairM r₁ r₁ && invPairM r₂ r₂ && Ws.all (fun w => invPairM w.2.2.1 w.2.2.2) &&
    fuseA8 r₁ r₂ Ws

@[expose] noncomputable def cmK (T W₁ W₂ : IT) (n M₁ M₂ : ℕ) (w : ℕ × ℕ × ℕ × ℕ) : Bool :=
  Nat.blt (T.find w.2.2.1 n) n &&
    if w.2.1 = 0 then M₁.testBit (T.find w.1 n) && W₁.find (T.find w.1 n) n == T.find w.2.2.1 n
    else w.2.1 == 1 && !M₁.testBit (T.find w.1 n) && M₂.testBit (T.find w.1 n) &&
      W₂.find (T.find w.1 n) n == T.find w.2.2.1 n

end CFSG.KC.C690

end

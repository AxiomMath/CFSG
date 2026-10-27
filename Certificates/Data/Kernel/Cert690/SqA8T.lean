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

@[expose] def tailL (l : List (Option ℕ)) : Bool :=
  l.all (fun o => o.isSome) && l.length == (l.filterMap fun o => o).length &&
    ((l.filterMap fun o => o).filter fun x => x == a0N).length == 120 &&
    [72, 336, 408, 672].contains ((l.filterMap fun o => o).filter fun x => x == z0N).length

@[expose] def invPair (g g' : ℕ) : Bool :=
  (List.range 64).all fun u => Code.act g (Code.act g' u) == u && Code.act g' (Code.act g u) == u

@[expose] noncomputable def a8T (r₁ r₂ : ℕ) (Ws : List (ℕ × ℕ × ℕ × ℕ)) : Bool :=
  invPair r₁ r₁ && invPair r₂ r₂ && Ws.all (fun w => invPair w.2.2.1 w.2.2.2) &&
    certBits.all fun b => tailL (valsT r₁ r₂ Ws b)

@[expose] noncomputable def cmK (T W₁ W₂ : IT) (n M₁ M₂ : ℕ) (w : ℕ × ℕ × ℕ × ℕ) : Bool :=
  Nat.blt (T.find w.2.2.1 n) n &&
    if w.2.1 = 0 then M₁.testBit (T.find w.1 n) && W₁.find (T.find w.1 n) n == T.find w.2.2.1 n
    else w.2.1 == 1 && !M₁.testBit (T.find w.1 n) && M₂.testBit (T.find w.1 n) &&
      W₂.find (T.find w.1 n) n == T.find w.2.2.1 n

end CFSG.KC.C690

end

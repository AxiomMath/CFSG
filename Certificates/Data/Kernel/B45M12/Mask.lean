module

public import CFSG.Quasithin.Background.SmithB45MatMask
public import CFSG.Quasithin.Background.SmithB45MatSpin

public section

namespace CFSG.KC.B45M12

open CFSG.Quasithin.H.Mathieu (actM)
open CFSG.Quasithin.B45Mat (mulM idM)

@[expose] noncomputable def eqL : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x y && eqL xs ys
  | _, _ => false

@[expose] noncomputable def eqM (m : ℕ) : List ℕ → List ℕ → Bool
  | [], Y => Y.all fun y => Nat.beq (y % 2 ^ m) 0
  | x :: xs, Y => Nat.beq (x % 2 ^ m) (Y.headD 0 % 2 ^ m) && eqM m xs Y.tail

@[expose] noncomputable def trStep : List ℕ → ℕ → List ℕ
  | [], _ => []
  | r :: rs, c => (2 * r + c % 2) :: trStep rs (c / 2)

@[expose] noncomputable def trM (m : ℕ) (X : List ℕ) : List ℕ :=
  X.foldr (fun c acc => trStep acc c) (List.replicate m 0)

@[expose] noncomputable def diag0 (n : ℕ) : List ℕ := 0 :: (idM n).tail

@[expose] noncomputable def subStep (m : ℕ) (B P T KB : List ℕ) : Bool :=
  eqL (mulM P KB) T && eqM m KB (mulM B T)

@[expose] noncomputable def subK (m d : ℕ) (B P : List ℕ) (KT : List (List ℕ × List ℕ)) : Bool :=
  Nat.ble B.length d && Nat.ble P.length m && eqM d (mulM P B) (idM d) &&
    KT.all fun p => Nat.ble p.1.length m && subStep m B P p.2 (mulM p.1 B)

@[expose] noncomputable def quotStep (d : ℕ) (B P K T PK : List ℕ) : Bool :=
  eqL (mulM P (mulM K B)) T && eqM d PK (mulM (mulM PK B) P)

@[expose] noncomputable def quotK (m d : ℕ) (B P : List ℕ) (KT : List (List ℕ × List ℕ)) :
    Bool :=
  Nat.ble B.length d && Nat.ble P.length m && eqM d (mulM P B) (idM d) &&
    KT.all fun p => Nat.ble p.1.length m && quotStep d B P p.1 p.2 (mulM P p.1)

@[expose] noncomputable def genM (Ga Gb : List ℕ) (z : ℕ) : List ℕ :=
  Bool.rec Ga Gb (Nat.beq z 2)

@[expose] noncomputable def wordT (Ha Hb : List ℕ) (w : List ℕ) (y : ℕ) : ℕ :=
  w.foldl (fun acc z => actM (genM Ha Hb z) acc) y

@[expose] noncomputable def sumT (Ha Hb : List ℕ) (terms : List (List ℕ × ℕ)) (y : ℕ) : ℕ :=
  terms.foldr (fun t acc => (if t.2 % 2 = 1 then wordT Ha Hb t.1 y else 0) ^^^ acc) 0

@[expose] noncomputable def spinR {α : Type} (f : ℕ → α → α) (v : α) :
    List (ℕ × ℕ) → ℕ → List α → List α
  | [], _, acc => acc
  | e :: es, k, acc =>
    spinR f v es (k + 1) (f e.2 (if e.1 < k then acc.getD (k - 1 - e.1) v else v) :: acc)

@[expose] noncomputable def spinM (Ga Gb : List ℕ) (v : ℕ) (prog : List (ℕ × ℕ)) : List ℕ :=
  (spinR (fun z x => actM (genM Ga Gb z) x) v prog 1 [v]).reverse

@[expose] noncomputable def col0 (Q : List ℕ) : ℕ := Q.foldr (fun r acc => r % 2 + 2 * acc) 0

@[expose] noncomputable def norF2 (n : ℕ) (tw : List (List ℕ)) (tc : List ℕ)
    (Q Qi R Si Ti : List ℕ) (w : ℕ) (spin dual : List (ℕ × ℕ)) (Ga Gb : List ℕ) : Bool :=
  let Ha := trM n Ga
  let Hb := trM n Gb
  let terms := tw.zip tc
  let v := col0 Q
  Nat.ble Ga.length n && Nat.ble Gb.length n && Nat.ble Q.length n &&
    Nat.beq (spin.length + 1) n && Nat.beq (dual.length + 1) n &&
    eqM n (mulM Q Qi) (idM n) &&
    eqM n (R.map fun r => actM Q (sumT Ha Hb terms r)) (diag0 n) &&
    eqM n (mulM (trM n Si) (spinM Ga Gb v spin)) (idM n) &&
    Nat.beq (sumT Ha Hb terms w % 2 ^ n) 0 &&
    eqM n (mulM (spinM Ha Hb w dual) Ti) (idM n)

end CFSG.KC.B45M12

end

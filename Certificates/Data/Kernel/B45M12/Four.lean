module

public import Certificates.Data.Kernel.B45M12.Mask

public section

namespace CFSG.KC.B45M12

@[expose] noncomputable def xorP (x y : ℕ × ℕ) : ℕ × ℕ := (x.1 ^^^ y.1, x.2 ^^^ y.2)

@[expose] noncomputable def smulP (s₀ s₁ : Bool) (c : ℕ × ℕ) : ℕ × ℕ :=
  match s₀, s₁ with
  | false, false => (0, 0)
  | true, false => c
  | false, true => (c.2, c.1 ^^^ c.2)
  | true, true => (c.1 ^^^ c.2, c.1)

@[expose] noncomputable def actF4 : List (ℕ × ℕ) → ℕ × ℕ → ℕ × ℕ
  | [], _ => (0, 0)
  | c :: cs, x =>
    xorP (smulP (Nat.beq (x.1 % 2) 1) (Nat.beq (x.2 % 2) 1) c) (actF4 cs (x.1 / 2, x.2 / 2))

@[expose] noncomputable def mulF4 (A B : List (ℕ × ℕ)) : List (ℕ × ℕ) := B.map (actF4 A)

@[expose] noncomputable def idF4 (n : ℕ) : List (ℕ × ℕ) := (List.range n).map fun j => (2 ^ j, 0)

@[expose] noncomputable def diag0F4 (n : ℕ) : List (ℕ × ℕ) := (0, 0) :: (idF4 n).tail

@[expose] noncomputable def eqF4 (m : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ) → Bool
  | [], Y => Y.all fun y => Nat.beq (y.1 % 2 ^ m) 0 && Nat.beq (y.2 % 2 ^ m) 0
  | x :: xs, Y =>
    Nat.beq (x.1 % 2 ^ m) ((Y.headD (0, 0)).1 % 2 ^ m) &&
      Nat.beq (x.2 % 2 ^ m) ((Y.headD (0, 0)).2 % 2 ^ m) && eqF4 m xs Y.tail

@[expose] noncomputable def trStepF4 : List (ℕ × ℕ) → ℕ × ℕ → List (ℕ × ℕ)
  | [], _ => []
  | r :: rs, c => (2 * r.1 + c.1 % 2, 2 * r.2 + c.2 % 2) :: trStepF4 rs (c.1 / 2, c.2 / 2)

@[expose] noncomputable def trF4 (m : ℕ) (X : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  X.foldr (fun c acc => trStepF4 acc c) (List.replicate m (0, 0))

@[expose] noncomputable def planes : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (0, 0)
  | k + 1, r =>
    let p := planes k (r / 4)
    (r % 2 + 2 * p.1, r / 2 % 2 + 2 * p.2)

@[expose] noncomputable def rowsF4 (n : ℕ) (rows : List ℕ) : List (ℕ × ℕ) := rows.map (planes n)

@[expose] noncomputable def colsF4 (n : ℕ) (rows : List ℕ) : List (ℕ × ℕ) :=
  trF4 n (rowsF4 n rows)

@[expose] noncomputable def ofF2 (X : List ℕ) : List (ℕ × ℕ) := X.map fun x => (x, 0)

@[expose] noncomputable def frobF4 (X : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  X.map fun c => (c.1 ^^^ c.2, c.2)

@[expose] noncomputable def subStepF4 (m : ℕ) (B P KB : List (ℕ × ℕ)) : Bool :=
  eqF4 m KB (mulF4 B (mulF4 P KB))

@[expose] noncomputable def subF4 (m d : ℕ) (B P : List (ℕ × ℕ)) (Ks : List (List (ℕ × ℕ))) :
    Bool :=
  Nat.ble B.length d && Nat.ble P.length m && eqF4 d (mulF4 P B) (idF4 d) &&
    Ks.all fun K => Nat.ble K.length m && subStepF4 m B P (mulF4 K B)

@[expose] noncomputable def genF4 (Ga Gb : List (ℕ × ℕ)) (z : ℕ) : List (ℕ × ℕ) :=
  Bool.rec Ga Gb (Nat.beq z 2)

@[expose] noncomputable def wordTF4 (Ha Hb : List (ℕ × ℕ)) (w : List ℕ) (y : ℕ × ℕ) : ℕ × ℕ :=
  w.foldl (fun acc z => actF4 (genF4 Ha Hb z) acc) y

@[expose] noncomputable def sumTF4 (Ha Hb : List (ℕ × ℕ)) (terms : List (List ℕ × ℕ))
    (y : ℕ × ℕ) : ℕ × ℕ :=
  terms.foldr (fun t acc =>
    xorP (smulP (Nat.beq (t.2 % 2) 1) (Nat.beq (t.2 / 2 % 2) 1) (wordTF4 Ha Hb t.1 y)) acc) (0, 0)

@[expose] noncomputable def spinF4M (Ga Gb : List (ℕ × ℕ)) (v : ℕ × ℕ) (prog : List (ℕ × ℕ)) :
    List (ℕ × ℕ) :=
  (spinR (fun z x => actF4 (genF4 Ga Gb z) x) v prog 1 [v]).reverse

@[expose] noncomputable def col0F4 (Q : List ℕ) : ℕ × ℕ :=
  Q.foldr (fun r acc => (r % 2 + 2 * acc.1, r / 2 % 2 + 2 * acc.2)) (0, 0)

@[expose] noncomputable def norF4 (n : ℕ) (tw : List (List ℕ)) (tc : List ℕ)
    (Q Qi R Si Ti : List ℕ) (w : ℕ) (spin dual : List (ℕ × ℕ)) (Ga Gb : List (ℕ × ℕ)) : Bool :=
  let Ha := trF4 n Ga
  let Hb := trF4 n Gb
  let terms := tw.zip tc
  let Q' := rowsF4 n Q
  let w' := planes n w
  let z := sumTF4 Ha Hb terms w'
  Nat.ble Ga.length n && Nat.ble Gb.length n && Nat.ble Q.length n &&
    Nat.beq (spin.length + 1) n && Nat.beq (dual.length + 1) n &&
    eqF4 n (mulF4 Q' (rowsF4 n Qi)) (idF4 n) &&
    eqF4 n ((rowsF4 n R).map fun r => actF4 Q' (sumTF4 Ha Hb terms r)) (diag0F4 n) &&
    eqF4 n (mulF4 (trF4 n (rowsF4 n Si)) (spinF4M Ga Gb (col0F4 Q) spin)) (idF4 n) &&
    Nat.beq (z.1 % 2 ^ n) 0 && Nat.beq (z.2 % 2 ^ n) 0 &&
    eqF4 n (mulF4 (spinF4M Ha Hb w' dual) (rowsF4 n Ti)) (idF4 n)

@[expose] noncomputable def traceGo : ℕ → List (ℕ × ℕ) → ℕ × ℕ
  | _, [] => (0, 0)
  | i, c :: cs => xorP (c.1 / 2 ^ i % 2, c.2 / 2 ^ i % 2) (traceGo (i + 1) cs)

@[expose] noncomputable def traceF4 (n : ℕ) (X : List (ℕ × ℕ)) : ℕ × ℕ := traceGo 0 (X.take n)

@[expose] noncomputable def traceK (n : ℕ) (X : List (ℕ × ℕ)) (c : ℕ) : Bool :=
  let t := traceF4 n X
  Nat.beq t.1 (c % 2) && Nat.beq t.2 (c / 2 % 2)

end CFSG.KC.B45M12

end

module

public import Certificates.Data.Kernel.E6WK

public section

namespace CFSG.KC.E6Div

open CFSG.KC.E6WK CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.StandardType.TwE6RootKill

@[expose] noncomputable def rc (vp r : ℕ) : ℕ := Nat.mod (Nat.shiftRight vp (Nat.mul 24 r)) 16777216

@[expose] noncomputable def csOf (vp p v : ℕ) : ℕ :=
  rc vp (lane p (lane v 0)) + Nat.shiftLeft (rc vp (lane p (lane v 1))) 24 +
  Nat.shiftLeft (rc vp (lane p (lane v 2))) 48 + Nat.shiftLeft (rc vp (lane p (lane v 3))) 72 +
  Nat.shiftLeft (rc vp (lane p (lane v 4))) 96 + Nat.shiftLeft (rc vp (lane p (lane v 5))) 120

@[expose] noncomputable def en (cs i j : ℕ) : ℕ :=
  Nat.mod (Nat.shiftRight cs (Nat.add (Nat.mul 24 j) (Nat.mul 4 i))) 16

@[expose] noncomputable def dl (i j : ℕ) : ℕ := Bool.rec 0 1 (Nat.beq i j)

@[expose] noncomputable def tP (a b c : ℕ) : ℕ := a * b * c + 64 * (a + b + c)

@[expose] noncomputable def tN (a b c : ℕ) : ℕ := 8 * (a * b + b * c + c * a) + 512

@[expose] noncomputable def okN (P N : ℕ) : Bool :=
  Bool.or' (Nat.beq P (N + 1)) (Bool.or' (Nat.beq P (N + 2))
    (Bool.or' (Nat.beq N (P + 1)) (Nat.beq N (P + 2))))

@[expose] noncomputable def det3N (a b d e f g h i j : ℕ) : Bool :=
  okN (tP a f j + tP b g h + tP d e i + tN d f h + tN a g i + tN b e j)
    (tN a f j + tN b g h + tN d e i + tP d f h + tP a g i + tP b e j)

@[expose] noncomputable def m3 (cs a b c x y z : ℕ) : Bool :=
  det3N (en cs a x + dl a x) (en cs a y + dl a y) (en cs a z + dl a z)
    (en cs b x + dl b x) (en cs b y + dl b y) (en cs b z + dl b z)
    (en cs c x + dl c x) (en cs c y + dl c y) (en cs c z + dl c z)

@[expose] noncomputable def ord3 (a b c : ℕ) : Bool :=
  Bool.and' (Nat.blt a b) (Bool.and' (Nat.blt b c) (Nat.blt c 6))

@[expose] noncomputable def ord2 (a b : ℕ) : Bool := Bool.and' (Nat.blt a b) (Nat.blt b 6)

@[expose] noncomputable def m3c (cs c : ℕ) : Bool :=
  Bool.and' (Bool.and' (ord3 (c % 8) (c / 8 % 8) (c / 64 % 8))
      (ord3 (c / 512 % 8) (c / 4096 % 8) (c / 32768 % 8)))
    (m3 cs (c % 8) (c / 8 % 8) (c / 64 % 8) (c / 512 % 8) (c / 4096 % 8) (c / 32768 % 8))

@[expose] noncomputable def det2N (a b e d : ℕ) : Bool :=
  okN (a * d + 8 * (b + e)) (b * e + 8 * (a + d))

@[expose] noncomputable def m2 (cs a b x y : ℕ) : Bool :=
  det2N (en cs a x - dl a x) (en cs a y - dl a y) (en cs b x - dl b x) (en cs b y - dl b y)

@[expose] noncomputable def m2c (cs c : ℕ) : Bool :=
  Bool.and' (Bool.and' (ord2 (c % 8) (c / 8 % 8)) (ord2 (c / 64 % 8) (c / 512 % 8)))
    (m2 cs (c % 8) (c / 8 % 8) (c / 64 % 8) (c / 512 % 8))

@[expose] noncomputable def sqE (cs i j : ℕ) : Bool :=
  let s := en cs i 0 * en cs 0 j + en cs i 1 * en cs 1 j + en cs i 2 * en cs 2 j +
    en cs i 3 * en cs 3 j + en cs i 4 * en cs 4 j + en cs i 5 * en cs 5 j
  let t := en cs i 0 + en cs 0 j + en cs i 1 + en cs 1 j + en cs i 2 + en cs 2 j +
    en cs i 3 + en cs 3 j + en cs i 4 + en cs 4 j + en cs i 5 + en cs 5 j
  Nat.beq (s + 384) (8 * t + dl i j)

@[expose] noncomputable def sqOne (cs : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun n ih => Bool.and' (sqE cs (n / 6) (n % 6)) ih) 36

@[expose] noncomputable def witC (cs c : ℕ) : Bool :=
  Bool.rec (Bool.and' (m3c cs ((c - 1) % 262144)) (m2c cs ((c - 1) / 262144))) (sqOne cs)
    (Nat.beq c 0)

@[expose] noncomputable def uCheckDiv (vp p : ℕ) (vk : List ℕ) : List ℕ → Bool :=
  @List.rec ℕ (fun _ => List ℕ → Bool)
    (fun ws => @List.rec ℕ (fun _ => Bool) true (fun _ _ _ => false) ws)
    (fun v _ ih ws => @List.rec ℕ (fun _ => Bool) false
      (fun c ws' _ => Bool.and' (witC (csOf vp p v) c) (ih ws')) ws) vk

@[expose] def negRhoOK (vp q : ℕ) : Bool :=
  (List.range 6).all fun j =>
    vecP vp (lane q j) == (List.range 6).map fun m => if m = wkRho.getD j 0 then -1 else 0

@[expose] def w0Check (vp ir : ℕ) (ω : List ℕ) : Bool :=
  ω.all (· < 6) && negRhoOK vp (wordPerm ir ω)

end CFSG.KC.E6Div

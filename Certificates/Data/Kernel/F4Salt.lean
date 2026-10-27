module

public import Certificates.Data.F4TwoSeitz
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.F4Salt

open CFSG.LieType.Simplicity.TitsBits CFSG.RankThree.PartOne.SEITZX CFSG.KC.Loop

@[expose] def dataS (A : ℕ) : ℕ :=
  A / 2 ^ 128 % 2 ^ 2704

@[expose] noncomputable def saltOf (r : ℕ) : ℕ :=
  Nat.add (Nat.shiftLeft r 128) (Nat.mod r (Nat.sub (Nat.pow 2 127) 1))

@[expose] noncomputable def maskOf (s : ℕ) : ℕ :=
  Nat.add (Nat.mul (Nat.pow 2 128) s) (Nat.sub (Nat.pow 2 64) 1)

@[expose] noncomputable def maskS : ℕ :=
  maskOf (slots 52)

@[expose] noncomputable def mulSAux (A B : ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun q ih =>
    Nat.xor (Nat.mul (Nat.mod (Nat.shiftRight A (Nat.add 128 (Nat.mul 52 q))) 4503599627370496)
      (Nat.land (Nat.shiftRight B q) maskS)) ih) n

@[expose] noncomputable def mulS (A B : ℕ) : ℕ :=
  strictN (Nat.shiftRight (mulSAux A B 52) 128) saltOf

@[expose] noncomputable def eqS (A B : ℕ) : Bool :=
  Nat.beq (Nat.mod (Nat.shiftRight A 128) (Nat.pow 2 2704))
    (Nat.mod (Nat.shiftRight B 128) (Nat.pow 2 2704))

@[expose] noncomputable def oneS : ℕ :=
  saltOf oneBits

@[expose] noncomputable def letS (c : ℕ) : ℕ :=
  saltOf (letterOfCode c).bits

@[expose] noncomputable def digit (W m : ℕ) : ℕ :=
  Nat.mod (Nat.shiftRight W (Nat.mul 3 m)) 8

@[expose] def decW8 (W : ℕ) : ℕ → List ℕ
  | 0 => []
  | L + 1 => decW8 W L ++ [W / 2 ^ (3 * L) % 8]

@[expose] noncomputable def wordSAux (W : ℕ) (m : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
    (fun m ih acc => strictN (mulS (letS (digit W m)) acc) ih) m

@[expose] noncomputable def wordS (W L : ℕ) : ℕ :=
  wordSAux W L oneS

end CFSG.KC.F4Salt

end

module

public import Certificates.Data.Kernel.B45M12.Four
public import CFSG.Quasithin.Background.SmithB45HM22Pack
public import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.KC.B45M22

open CFSG.KC.B45M12

@[expose] noncomputable def colsK (n : ℕ) (f : ℕ → ℕ) (cols : List ℕ) : Bool :=
  Nat.beq cols.length n && (List.range n).all fun j => Nat.beq (f (2 ^ j)) (cols.getD j 0)

@[expose] noncomputable def deint : ℕ → ℕ → ℕ × ℕ
  | 0, r => (r % 2, r / 2 % 2)
  | k + 1, r =>
    cond (Nat.beq r 0) (0, 0)
      (let lo := deint k (r % 4 ^ 2 ^ k)
       let hi := deint k (r / 4 ^ 2 ^ k)
       (lo.1 + 2 ^ 2 ^ k * hi.1, lo.2 + 2 ^ 2 ^ k * hi.2))

@[expose] noncomputable def colsD (n k : ℕ) (rows : List ℕ) : List (ℕ × ℕ) :=
  trF4 n (rows.map (deint k))

@[expose] noncomputable def k340 (C T : List ℕ) : List (ℕ × ℕ) :=
  CFSG.Quasithin.HM22.PM.kron 10 34 (ofF2 C) (ofF2 T)

@[expose] noncomputable def subStepF4K (m d : ℕ) (B P T KB : List (ℕ × ℕ)) : Bool :=
  eqF4 d (mulF4 P KB) T && eqF4 m KB (mulF4 B T)

@[expose] noncomputable def subF4K (m d : ℕ) (B P : List (ℕ × ℕ))
    (KT : List (List (ℕ × ℕ) × List (ℕ × ℕ))) : Bool :=
  Nat.ble B.length d && Nat.ble P.length m && eqF4 d (mulF4 P B) (idF4 d) &&
    KT.all fun p => Nat.ble p.1.length m && subStepF4K m d B P p.2 (mulF4 p.1 B)

end CFSG.KC.B45M22

end

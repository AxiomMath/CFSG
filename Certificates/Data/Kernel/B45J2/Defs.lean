module

public import Certificates.Data.Kernel.B45M12.Four

public section

namespace CFSG.KC.B45J2

open CFSG.KC.B45M12

@[expose] noncomputable def rowOf : List ℕ → ℕ
  | [] => 0
  | l :: ls => l % 2 ^ 60 + 2 ^ 60 * rowOf ls

@[expose] noncomputable def rowsL (k : ℕ) : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | m + 1, L => rowOf (L.take k) :: rowsL k m (L.drop k)

@[expose] noncomputable def colsL (m n : ℕ) (L : List ℕ) : List (ℕ × ℕ) :=
  colsF4 n (rowsL ((n + 29) / 30) m L)

@[expose] noncomputable def shiftsF4 (n : ℕ) : ℕ → ℕ × ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | k + 1, c => c :: shiftsF4 n k (c.1 * 2 ^ n, c.2 * 2 ^ n)

@[expose] noncomputable def kronF4 (m n : ℕ) (A B : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  A.flatMap fun x => B.map fun y => actF4 (shiftsF4 n m (y.1 % 2 ^ n, y.2 % 2 ^ n)) x

@[expose] noncomputable def wordF4 (n : ℕ) (Ga Gb : List (ℕ × ℕ)) : List Bool → List (ℕ × ℕ)
  | [] => idF4 n
  | [z] => Bool.rec Ga Gb z
  | z :: y :: w => mulF4 (Bool.rec Ga Gb z) (wordF4 n Ga Gb (y :: w))

@[expose] noncomputable def pinF4 (m d : ℕ) (B P KB T : List (ℕ × ℕ)) : Bool :=
  eqF4 d (mulF4 P KB) T && eqF4 m KB (mulF4 B T)

@[expose] noncomputable def subKF4 (m d : ℕ) (B P : List (ℕ × ℕ))
    (KT : List (List (ℕ × ℕ) × List (ℕ × ℕ))) : Bool :=
  Nat.ble B.length d && Nat.ble P.length m && eqF4 d (mulF4 P B) (idF4 d) &&
    KT.all fun kt => Nat.ble kt.1.length m && Nat.beq kt.2.length d &&
      pinF4 m d B P (mulF4 kt.1 B) kt.2

@[expose] noncomputable def norL (n : ℕ) (tw : List (List ℕ)) (tc : List ℕ)
    (Q Qi R Si Ti w : List ℕ) (spin dual : List (ℕ × ℕ)) (Ga Gb : List (ℕ × ℕ)) : Bool :=
  norF4 n tw tc (rowsL ((n + 29) / 30) n Q) (rowsL ((n + 29) / 30) n Qi)
    (rowsL ((n + 29) / 30) n R) (rowsL ((n + 29) / 30) n Si) (rowsL ((n + 29) / 30) n Ti)
    (rowOf (w.take ((n + 29) / 30))) spin dual Ga Gb

end CFSG.KC.B45J2

end

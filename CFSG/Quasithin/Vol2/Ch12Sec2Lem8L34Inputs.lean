module

public import CFSG.Fischer.F4
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.H13.L34

open Matrix CFSG.Fischer CFSG.Assembly.LowTwoRank

@[expose] def cadd (x y : Fin 4) : Fin 4 := x ^^^ y

@[expose] def cmul (x y : Fin 4) : Fin 4 :=
  ⟨(x.val % 2 * (y.val % 2) + x.val / 2 * (y.val / 2)) % 2 +
    2 * ((x.val % 2 * (y.val / 2) + x.val / 2 * (y.val % 2) + x.val / 2 * (y.val / 2)) % 2),
    by omega⟩

structure M3 where
  a00 : Fin 4
  a01 : Fin 4
  a02 : Fin 4
  a10 : Fin 4
  a11 : Fin 4
  a12 : Fin 4
  a20 : Fin 4
  a21 : Fin 4
  a22 : Fin 4
deriving DecidableEq

namespace M3

@[expose] def add3 (x y z : Fin 4) : Fin 4 := cadd (cadd x y) z

@[expose] def mul (A B : M3) : M3 :=
  ⟨add3 (cmul A.a00 B.a00) (cmul A.a01 B.a10) (cmul A.a02 B.a20),
    add3 (cmul A.a00 B.a01) (cmul A.a01 B.a11) (cmul A.a02 B.a21),
    add3 (cmul A.a00 B.a02) (cmul A.a01 B.a12) (cmul A.a02 B.a22),
    add3 (cmul A.a10 B.a00) (cmul A.a11 B.a10) (cmul A.a12 B.a20),
    add3 (cmul A.a10 B.a01) (cmul A.a11 B.a11) (cmul A.a12 B.a21),
    add3 (cmul A.a10 B.a02) (cmul A.a11 B.a12) (cmul A.a12 B.a22),
    add3 (cmul A.a20 B.a00) (cmul A.a21 B.a10) (cmul A.a22 B.a20),
    add3 (cmul A.a20 B.a01) (cmul A.a21 B.a11) (cmul A.a22 B.a21),
    add3 (cmul A.a20 B.a02) (cmul A.a21 B.a12) (cmul A.a22 B.a22)⟩

@[expose] def det (A : M3) : Fin 4 :=
  cadd (add3 (cmul A.a00 (cmul A.a11 A.a22)) (cmul A.a01 (cmul A.a12 A.a20))
      (cmul A.a02 (cmul A.a10 A.a21)))
    (add3 (cmul A.a02 (cmul A.a11 A.a20)) (cmul A.a01 (cmul A.a10 A.a22))
      (cmul A.a00 (cmul A.a12 A.a21)))

@[expose] def IsScalar (A : M3) : Prop :=
  A.a01 = 0 ∧ A.a02 = 0 ∧ A.a10 = 0 ∧ A.a12 = 0 ∧ A.a20 = 0 ∧ A.a21 = 0 ∧ A.a00 = A.a11 ∧
    A.a11 = A.a22

instance (A : M3) : Decidable A.IsScalar := by
  unfold IsScalar
  infer_instance

@[expose] def all : List M3 := do
  let xs : List (Fin 4) := [0, 1, 2, 3]
  let a00 ← xs
  let a01 ← xs
  let a02 ← xs
  let a10 ← xs
  let a11 ← xs
  let a12 ← xs
  let a20 ← xs
  let a21 ← xs
  let a22 ← xs
  pure ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩

@[expose] def check (A : M3) : Bool :=
  let A2 := mul A A
  let A3 := mul A2 A
  let A5 := mul A3 A2
  let A15 := mul (mul A5 A5) A5
  !(decide (det A = 1)) || !(decide A15.IsScalar) || decide A5.IsScalar || decide A3.IsScalar

end M3

end CFSG.Quasithin.H13.L34

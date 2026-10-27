module

public import CFSG.Monster.Code.Bits

public noncomputable section

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster.Code

@[expose] def gramRows : List ℕ := [128, 192, 56, 52, 44, 28, 130, 67]

@[expose] def gram0 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => bvec 8 (gramRows.getD i 0) j

@[expose] def qPoly (v : Fin 8 → ZMod 2) : ZMod 2 :=
  (∑ i : Fin 8, ∑ j : Fin 8, if i < j then gram0 i j * v i * v j else 0) + v 6 + v 7

end CFSG.Monster.B.TwoA.Sp8

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B.TwoA.Sp8

@[expose] def K1Bad (v : Fin 8 → ZMod 2) : Prop :=
  qPoly v = 0 ∧ qPoly (Pi.single 0 1 + v) = 1

@[expose] def K1Edge (v w : Fin 8 → ZMod 2) : Prop :=
  v ≠ w ∧ qPoly (v + w) = 0 ∧ qPoly (Pi.single 0 1 + v + w) = 0

abbrev k1Root : Fin 8 → ZMod 2 := Pi.single 0 1 + Pi.single 7 1

instance (v : Fin 8 → ZMod 2) : Decidable (K1Bad v) := by
  unfold K1Bad
  infer_instance

instance (v w : Fin 8 → ZMod 2) : Decidable (K1Edge v w) := by
  unfold K1Edge
  infer_instance

end CFSG.Monster.B.GSide

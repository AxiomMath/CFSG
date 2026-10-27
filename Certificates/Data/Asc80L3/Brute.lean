module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.Quasithin.E2P.Asc80

abbrev M3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 3)

@[expose] def uM : M3 := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def uM' : M3 := !![1, -1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def lM : M3 := !![1, 0, 0; 1, 1, 0; 0, 0, 1]

@[expose] def lM' : M3 := !![1, 0, 0; -1, 1, 0; 0, 0, 1]

@[expose] def det3 (a b c d e f g h i : ZMod 3) : ZMod 3 :=
  a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g

@[expose] def BruteTwo : Prop :=
  ∀ a b c d e f g h i : ZMod 3, det3 a b c d e f g h i = 1 →
    (!![a, b, c; d, e, f; g, h, i] : M3) * !![a, b, c; d, e, f; g, h, i] = 1 →
    (!![a, b, c; d, e, f; g, h, i] : M3) ≠ 1 →
    (!![a, b, c; d, e, f; g, h, i] : M3) *
      (uM * !![a, b, c; d, e, f; g, h, i] * uM') =
      (uM * !![a, b, c; d, e, f; g, h, i] * uM') * !![a, b, c; d, e, f; g, h, i] →
    (!![a, b, c; d, e, f; g, h, i] : M3) *
      (lM * !![a, b, c; d, e, f; g, h, i] * lM') =
      (lM * !![a, b, c; d, e, f; g, h, i] * lM') * !![a, b, c; d, e, f; g, h, i] →
    (!![a, b, c; d, e, f; g, h, i] : M3) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

@[expose] def BruteThirteen : Prop :=
  ∀ a b c d e f g h i : ZMod 3, det3 a b c d e f g h i = 1 →
    (!![a, b, c; d, e, f; g, h, i] : M3) *
      (uM * !![a, b, c; d, e, f; g, h, i] * uM') =
      (uM * !![a, b, c; d, e, f; g, h, i] * uM') * !![a, b, c; d, e, f; g, h, i] →
    (!![a, b, c; d, e, f; g, h, i] : M3) ^ 13 = 1 → (!![a, b, c; d, e, f; g, h, i] : M3) = 1

end CFSG.Quasithin.E2P.Asc80

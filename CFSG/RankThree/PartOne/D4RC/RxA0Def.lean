module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.D4RC

open scoped MatrixGroups

@[expose] def rclA0AlgOf (L : Type) [Field L] (k : Type) [Field k] [Algebra k L]
    (H' : SL(3, L)) : Subgroup SL(3, L) :=
  Subgroup.closure {X | ∃ t : k, X = H' * Matrix.SpecialLinearGroup.transvection
    (show (0 : Fin 3) ≠ 1 by decide) (algebraMap k L t) * H'⁻¹}

end CFSG.RankThree.PartOne.D4RC

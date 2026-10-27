module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.GroupTheory.CommutatorProductCard
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def IsTransvectionMat {n : ℕ} {K : Type} [Field K] (g : GL (Fin n) K) : Prop :=
  ((g : Matrix (Fin n) (Fin n) K) - 1) * ((g : Matrix (Fin n) (Fin n) K) - 1) = 0 ∧
    Matrix.rank ((g : Matrix (Fin n) (Fin n) K) - 1) = 1

end CFSG.RankThree.GF2n.Smith81

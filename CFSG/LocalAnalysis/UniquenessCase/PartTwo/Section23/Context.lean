module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure Ctx23 (D : Data G) (Ch : Choice2011 G) extends Ctx21 D Ch where
  hTI : CFSG.CGT.Timmesfeld75.IsTI D.U

structure Ctx23L (D : Data G) (Ch : Choice2011 G) extends Ctx23 D Ch where
  L : Subgroup G
  hL : L ∈ calLStar D.T D.M
  hL0L : L0 ≤ L
  N : Subgroup G
  hN : calMOf (L ⊔ D.T) = {N}

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

@[expose] def V : Subgroup G := conjClosure c.N D.Z

@[expose] def U0 : Subgroup G := conjClosure (c.N ⊓ D.M) D.Z

@[expose] def E : Subgroup G := conjClosure D.M c.V

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

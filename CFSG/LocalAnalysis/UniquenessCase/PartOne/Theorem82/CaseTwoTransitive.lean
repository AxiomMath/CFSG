module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.Ctx812
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

structure CaseTwoTransitive (c : Ctx812E G) where
  d : SylowThreeData G
  hdM : d.M = c.S.M
  hdL : d.L = c.L
  hinj : Function.Injective d.Lf
  hcomp : ∀ i, CFSG.Yardstones.Mf4cdcdf2e013.Asc83CComponent c.S.M (d.Lf i)
  hperm : ∀ m ∈ c.S.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j
  P : Subgroup G
  hP : CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M
  hdS : d.S = P ⊓ c.L
  y : G
  hyP : y ∈ P
  hy3 : y ^ 3 = 1
  hyL : ∀ i, (d.Lf i).map (MulAut.conj y).toMonoidHom = d.Lf (i + 1)
  hPy : d.S ⊔ Subgroup.zpowers y = P

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

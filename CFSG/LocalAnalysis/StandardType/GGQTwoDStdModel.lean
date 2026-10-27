module

public import CFSG.ClassicalInvolution.Phan.PhanDn.StdFamily
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.Defs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Basic
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanEDefs
public import CFSG.RankThree.PartOne.CTP.ExtPhan

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits

section Model

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

@[expose] noncomputable def qtwoStdU (E : QuadExt F K (unitaryInvolution K 2 1)) (m : ℕ)
    (hm : 3 ≤ m) (k : Fin (m + 1)) : Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
  ((stdFamilyV E m hm).ι k).range

@[expose] noncomputable def qtwoStdW (E : QuadExt F K (unitaryInvolution K 2 1)) (m : ℕ)
    (hm : 3 ≤ m) (i j : Fin (m + 1)) :
    Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) :=
  if CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 3 then
    (if i < j then ((stdFamilyV E m hm).θ i j).range else ((stdFamilyV E m hm).θ j i).range)
  else qtwoStdU E m hm i ⊔ qtwoStdU E m hm j

end Model

end CFSG.StandardType.QTwo

end

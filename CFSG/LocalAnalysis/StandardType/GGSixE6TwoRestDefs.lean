module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoModel

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

@[expose] noncomputable def cOmegaE
    (k : Fin 3) : EC :=
  xr (a5Root (blk k 0) (blk k 1)) * xr (a5Root (blk k 1) (blk k 0))

@[expose] noncomputable def wOmegaE :
    EC :=
  cOmegaE 0 * cOmegaE 1 * cOmegaE 2

@[expose] noncomputable def dE :
    Subgroup EC :=
  Subgroup.closure {zE, wOmegaE}

@[expose] noncomputable def rE :
    Subgroup EC :=
  Subgroup.closure {rOne 0 2, rOmega 0 2}

@[expose] noncomputable def rmE :
    Subgroup EC :=
  Subgroup.closure {rOne 2 0, rOmega 2 0}

@[expose] noncomputable def j0E :
    Subgroup EC :=
  rE ⊔ rmE

@[expose] def lamE : Fin Tag.E6.rank → ℤ :=
  a5Root 0 4 + a5Root 1 5

@[expose] def qRoots : Set (Fin Tag.E6.rank → ℤ) :=
  {β | IsRoot .E6 β ∧ 0 < iform β lamE}

@[expose] def zRoots : Set (Fin Tag.E6.rank → ℤ) :=
  {β | IsRoot .E6 β ∧ iform β lamE = 2}

@[expose] noncomputable def qE :
    Subgroup EC :=
  (rootSpan .E6 F2 qRoots).subgroupOf (adjointGroup .E6 F2)

@[expose] noncomputable def z0E :
    Subgroup EC :=
  (rootSpan .E6 F2 zRoots).subgroupOf (adjointGroup .E6 F2)

@[expose] def mu1List : List (Fin Tag.E6.rank → ℤ) :=
  [![-1, -1, -1, -1, 0, 0], ![0, -1, -1, -1, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1], ![0, 1, 1, 2, 2, 1], ![1, 1, 1, 2, 2, 1]]

@[expose] def mu2List : List (Fin Tag.E6.rank → ℤ) :=
  [![0, -1, 0, -1, -1, -1], ![0, -1, 0, -1, -1, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0],
    ![1, 0, 1, 0, 0, 0], ![1, 0, 1, 1, 0, 0], ![1, 1, 2, 2, 1, 0], ![1, 1, 2, 2, 1, 1]]

@[expose] noncomputable def uMu1 :
    Subgroup EC :=
  (rootSpan .E6 F2 {β | β ∈ mu1List}).subgroupOf (adjointGroup .E6 F2)

@[expose] noncomputable def uMu2 :
    Subgroup EC :=
  (rootSpan .E6 F2 {β | β ∈ mu2List}).subgroupOf (adjointGroup .E6 F2)

end CFSG.StandardType.GGSixE6Two

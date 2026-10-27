module

public import CFSG.GH74.KGroups.FieldGF
public import CFSG.LieType.SeitzGeneration.HeisSmallCheck

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.GH74.KGroups CFSG.LieType.SeitzGeneration.HeisSmall

@[expose] def tMat : M3 GF16 :=
  ⟨GF16.ofNat' 0, GF16.ofNat' 1, GF16.ofNat' 0,
    GF16.ofNat' 1, GF16.ofNat' 0, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 0, GF16.ofNat' 1⟩

@[expose] def x1Mat : M3 GF16 :=
  ⟨GF16.ofNat' 15, GF16.ofNat' 0, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 10, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 0, GF16.ofNat' 10⟩

@[expose] def x1InvMat : M3 GF16 :=
  ⟨GF16.ofNat' 8, GF16.ofNat' 0, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 12, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 0, GF16.ofNat' 12⟩

@[expose] def x2Mat : M3 GF16 :=
  ⟨GF16.ofNat' 9, GF16.ofNat' 13, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 0, GF16.ofNat' 15,
    GF16.ofNat' 7, GF16.ofNat' 9, GF16.ofNat' 0⟩

@[expose] def x2InvMat : M3 GF16 :=
  ⟨GF16.ofNat' 14, GF16.ofNat' 0, GF16.ofNat' 7,
    GF16.ofNat' 11, GF16.ofNat' 0, GF16.ofNat' 14,
    GF16.ofNat' 0, GF16.ofNat' 8, GF16.ofNat' 0⟩

@[expose] def d1Mat : M3 GF16 :=
  ⟨GF16.ofNat' 8, GF16.ofNat' 0, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 15, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 0, GF16.ofNat' 1⟩

@[expose] def d2Mat : M3 GF16 :=
  ⟨GF16.ofNat' 12, GF16.ofNat' 7, GF16.ofNat' 3,
    GF16.ofNat' 6, GF16.ofNat' 10, GF16.ofNat' 5,
    GF16.ofNat' 4, GF16.ofNat' 2, GF16.ofNat' 0⟩

@[expose] def y1Mat : M3 GF16 :=
  ⟨GF16.ofNat' 15, GF16.ofNat' 0, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 15, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 0, GF16.ofNat' 12⟩

@[expose] def y1InvMat : M3 GF16 :=
  ⟨GF16.ofNat' 8, GF16.ofNat' 0, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 8, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 0, GF16.ofNat' 10⟩

@[expose] def y2Mat : M3 GF16 :=
  ⟨GF16.ofNat' 9, GF16.ofNat' 9, GF16.ofNat' 15,
    GF16.ofNat' 13, GF16.ofNat' 8, GF16.ofNat' 2,
    GF16.ofNat' 0, GF16.ofNat' 6, GF16.ofNat' 13⟩

@[expose] def y2InvMat : M3 GF16 :=
  ⟨GF16.ofNat' 14, GF16.ofNat' 11, GF16.ofNat' 0,
    GF16.ofNat' 14, GF16.ofNat' 15, GF16.ofNat' 6,
    GF16.ofNat' 8, GF16.ofNat' 3, GF16.ofNat' 11⟩

@[expose] def e1Mat : M3 GF16 :=
  ⟨GF16.ofNat' 10, GF16.ofNat' 0, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 10, GF16.ofNat' 0,
    GF16.ofNat' 0, GF16.ofNat' 0, GF16.ofNat' 15⟩

@[expose] def e2Mat : M3 GF16 :=
  ⟨GF16.ofNat' 3, GF16.ofNat' 15, GF16.ofNat' 7,
    GF16.ofNat' 15, GF16.ofNat' 6, GF16.ofNat' 5,
    GF16.ofNat' 7, GF16.ofNat' 5, GF16.ofNat' 0⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

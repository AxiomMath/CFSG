module

public import CFSG.LieType.BorelTits.OrthogonalEven
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

open Matrix CFSG.Open CFSG.LieType.BorelTits

abbrev Idx : Type := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2

abbrev Omega6 (F : Type) [Field F] (b c : F) : Subgroup (GL Idx F) :=
  StatedOmega (StatedQuadMinus 3 F b c)

noncomputable abbrev Phi6 {F : Type} [Field F] [Finite F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : QuadForm F (Idx → F) :=
  quadMinusForm 3 F b c hirr

noncomputable abbrev Rep6 (F : Type) [Field F] (b c : F) :
    ↥(Omega6 F b c) →* Module.End F (Idx → F) :=
  natRep (Omega6 F b c)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.O6m4FF

module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

abbrev linE13 (F' : Type) [Field F'] : Matrix (Fin 3) (Fin 3) F' := Matrix.single 0 2 1

abbrev linConj {F' : Type} [Field F'] (τ : SpecialLinearGroup (Fin 3) F') :
    Matrix (Fin 3) (Fin 3) F' :=
  ((τ⁻¹ : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') * linE13 F' *
    (τ : Matrix (Fin 3) (Fin 3) F')

abbrev linZ (F' : Type) [Field F'] : Subgroup (SpecialLinearGroup (Fin 3) F') :=
  (center ↥(unitriangular 3 F')).map (unitriangular 3 F').subtype

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard

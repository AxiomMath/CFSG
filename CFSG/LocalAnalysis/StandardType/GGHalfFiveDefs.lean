module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveCommutant

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

variable {G : Type} [Group G]

@[expose] noncomputable def bElt (φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G) : G :=
  φ₁ zeta5 * φ₂ (omegaBlock 5 4)

@[expose] noncomputable def dPrime (x : G) (φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G) :
    Subgroup G :=
  Subgroup.closure {x, bElt φ₁ φ₂}

end CFSG.StandardType.GGHalf

end

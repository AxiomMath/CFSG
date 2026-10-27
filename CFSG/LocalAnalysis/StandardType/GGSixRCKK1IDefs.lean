module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRG
public import CFSG.LocalAnalysis.StandardType.GGLieOddCoverDefs

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)

@[expose] def RCKRootFieldExact {U : Type*} [Group U] (R : Subgroup U) (Fq : Type) [Field Fq]
    (ε : Multiplicative Fq ≃* R) : Prop :=
  (∀ l : Fq, l ≠ 0 → ∃ h : U, ∀ t : Fq,
    h * (ε (Multiplicative.ofAdd t) : U) * h⁻¹ = ε (Multiplicative.ofAdd (l * t))) ∧
  ∀ n ∈ Subgroup.normalizer (R : Set U), ∃ l : Fq, l ≠ 0 ∧ ∀ t : Fq,
    n * (ε (Multiplicative.ofAdd t) : U) * n⁻¹ = ε (Multiplicative.ofAdd (l * t))

end CFSG.StandardType.RCKK1I

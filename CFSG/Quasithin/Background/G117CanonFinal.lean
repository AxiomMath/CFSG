module

public import CFSG.Quasithin.Background.G117CanonLtMain
import CFSG.Quasithin.Background.G93Apply
public import CFSG.Quasithin.Background.Harris.HoldsDimensionOnly
public import CFSG.Quasithin.Background.SzG11M12Main
import CFSG.Quasithin.Background.SzG11TwoOm4
import CFSG.Quasithin.Background.SzG11TwoSp4
import CFSG.Quasithin.Background.SzG11TwoG2
public import CFSG.Quasithin.Background.G117M22
public import CFSG.Quasithin.Background.P3G2
import CFSG.Quasithin.Background.P3OrthoA8Fact
import CFSG.Quasithin.Background.E11Main
public import CFSG.Quasithin.Background.G117CanonSteps3
public import CFSG.Quasithin.Background.SzG11SNC

public section

namespace CFSG.Quasithin

namespace G11

namespace Canon

section G117Canon


theorem g11_7_canon
    {Q : ConclPred} (hQ : QContains Q) :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
      (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
      QSetup Q B Γ v₁ W X X₀ L → ∀ I : Submodule (ZMod 2) V, G116Props B Γ v₁ X L I →
        ¬ FaithfulOn X I ∧ I ≠ ⊤ :=
  g11_7_of_steps Q hQ (g93_apply Harris.g93StmtDimensionOnly_holds)
    SzG11S.noConfigM12 SzG11S.noConfigL2
    (SzG11S.noConfigOm4Minus_of_two SzG11S.noConfigOm4MinusTwo)
    (SzG11S.noConfigSp4_of_two SzG11S.noConfigSp4Two) SzG11S.noConfigOm4Plus
    SzG11S.noConfigOm4PlusFour G117.autHatM22Bound a8OrthogonalFact om4Plus4Iso
    (step10 hQ (SzG11S.noConfigG2_of_two SzG11S.noConfigG2Two) g22DerivedFacts)
    (stepLt e11 G117.a6NormalizerBound G117.a6Facts hQ)

end G117Canon

end Canon

end G11

end CFSG.Quasithin

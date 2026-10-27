module

public import CFSG.Quasithin.H13.L32NItems143b
public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def Lemma14323Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V), Module.finrank (ZMod 2) D.V = 4 →
      Case14323i T L V g D ∨ Case14323ii T V g D ∨ Case14323iii T V g D ∨
        Case14323iv T L V D

@[expose] def Lemma14324Big : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    fsuV1 T V < centerOf (fsuU T V) →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V), 6 ≤ Module.finrank (ZMod 2) D.V →
      G112Concl6 (D.img (l32nH T V)) ∧
        G11.IsG2NaturalModule (D.img (l32nH T V))
          (quasithinG2 (GaloisField 2 1))

end CFSG.Quasithin.H13

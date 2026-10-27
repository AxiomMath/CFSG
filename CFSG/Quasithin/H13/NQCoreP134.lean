module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Vol2.Ch1Xi

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native

@[expose] def Prop134ThreeExtraspecial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H S X P : Subgroup G),
    CFSG.SectionRank.IsSQTKCat ↥H → pCoreOf 2 H ≠ ⊥ → IsSylowTwoOf S H → X ≤ H → IsXi S X →
    (pCoreOf 2 X).relIndex X = 27 → P ≤ X → IsPGroup 3 P → Nat.card P = 27 →
    H ≤ Subgroup.normalizer (X : Set G)

end CFSG.Quasithin.H13.NQCore

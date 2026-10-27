module

public import CFSG.Quasithin.Vol2.Ch1Xi
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def Lemma139Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G], quasithinIsQTKECat G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → ∀ T X L : Subgroup G, quasithinIsSylowTwo T → IsXiF T X →
      quasithinIsLocal T L → X ≤ conjClosure L T →
      VYR X (centralizerSection (T ⊓ conjClosure L T) X (pCoreOf 2 X)) ≤
          VY (conjClosure L T) ∧
        quasithinIsFaithfulLocal T L

end CFSG.Quasithin.H13.NQCore

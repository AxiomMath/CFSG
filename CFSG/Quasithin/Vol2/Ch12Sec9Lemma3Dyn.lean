module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S146B0

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def DynkinFact1293SL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (B K S : Subgroup X), B ≤ K → IsSL2 7 ↥B →
    (∃ s : Bool, IsPSLEps3 s 7 1 ↥K ∨ IsSLEps3 s 7 ↥K) →
    QuasithinUnique.IsSylowTwoOf S K → S ≤ Subgroup.normalizer (B : Set X) →
    ∃ s ∈ S, KbarInducesOuter B s

end CFSG.Quasithin.H13

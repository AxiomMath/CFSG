module

public import CFSG.Quasithin.EmptyFaithful.S1421Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Q16Irred (G : Type) [Group G] (T K1 : Subgroup G) : Prop :=
  ∀ W : Subgroup G, quasithinOmegaOneCenter T ≤ W → W ≤ pCoreOf 2 K1 →
    (∀ k ∈ K1, ∀ w ∈ W, k * w * k⁻¹ ∈ W) → W = quasithinOmegaOneCenter T ∨ W = pCoreOf 2 K1

@[expose] def Lemma14216QIrred4LegacyBare : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    Survivor4LegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) → Q16Irred G T K1

end CFSG.Quasithin

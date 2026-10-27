module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKSD

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

@[expose] def NSBLocalFlipFiveThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L Mm I H K : Subgroup G) (m k j : ℕ),
    ChoiceCh G T M L Mm I H K m k → I ≤ Subgroup.normalizer (vV T L : Set G) → m = 3 →
      j + 1 ≤ 5 → k ≤ j → StdData G T L I K m k 5 j →
      ∀ g : G, g ∈ (K ⊔ pCoreOf 2 I) ⊔ gammaZero T M L I →
        (∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I) → (∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I) →
          (∃ u ∈ uZero I K, g⁻¹ * u * g ∉
            kerA (K ⊔ pCoreOf 2 I) (gammaZero T M L I)) → False

end CFSG.Quasithin.H13.Ch4.NSB

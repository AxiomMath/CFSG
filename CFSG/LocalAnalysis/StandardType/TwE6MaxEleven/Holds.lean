module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoBridgeDefs
public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Main
public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Model
public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Filter
public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Levi
public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.TwoLocal
public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Sporadic

public section

namespace CFSG.StandardType.TwE6MaxEleven

open CFSG.Blueprint CFSG.Assembly

section Leaves


theorem ggTwistedE6MaxElevenInput_of_leaves (hSp : SporadicFacts) (hE : ElevenSimpleCases)
    (hlevi : ∀ (X : Type) [Group X] [Finite X], ChevalleyExceptionalModel X .twistedE6 2 1 →
      ∃ y₀ : X, orderOf y₀ = 3 ∧ ∃ L : Subgroup X,
        L ≤ Subgroup.centralizer ({y₀} : Set X) ∧ Nat.card L = 9196830720 ∧
        ∀ P : Subgroup X, P ≤ Subgroup.centralizer ({y₀} : Set X) → ⁅P, P⁆ = P → P ≤ L)
    (htwo : ∀ (X : Type) [Group X] [Finite X], ChevalleyExceptionalModel X .twistedE6 2 1 →
      ∀ M : Subgroup X, IsCoatom M → ∀ U : Subgroup X, U ≠ ⊥ → IsPGroup 2 U →
        M ≤ Subgroup.normalizer (U : Set X) → ¬ 3 ^ 7 ∣ Nat.card M) :
    GGTwistedE6MaxElevenInput := by
  intro X _ _ hX hK M hM h11
  have hLF : LocalFacts X :=
    ⟨card_of_model hX, isSimpleGroup_of_model hX, c11_of_model hX, c17_of_model hX,
      rank3_of_model hX, elem11_of_model hX, hlevi X hX, htwo X hX⟩
  exact Or.inr (maxElevenProp_of_facts hSp hE hLF hK hM h11)

end Leaves

section Final


theorem ggTwistedE6MaxElevenInput_of_sporadicFacts (hSp : SporadicFacts) :
    GGTwistedE6MaxElevenInput :=
  ggTwistedE6MaxElevenInput_of_leaves hSp elevenSimpleCases_holds (fun _ _ _ h => levi_of_model h)
    (fun _ _ _ h => twoLocal_of_model h)

theorem ggTwistedE6MaxElevenInput_holds : GGTwistedE6MaxElevenInput :=
  ggTwistedE6MaxElevenInput_of_sporadicFacts sporadicFacts_holds

end Final

end CFSG.StandardType.TwE6MaxEleven

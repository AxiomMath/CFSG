module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9Types

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped Pointwise commutatorElement

@[expose] def Lemma15123FiveInputC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15120Types T Mc M Z₁ L →
    Lemma15121Concl Mc Z₁ L → Ce15Six T Mc M 5 →
    (∃ Y' : Subgroup G, Y' ≤ M ⊓ g1_1516 Z₁ ∧ Y' ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
      IsPGroup 5 Y' ∧
      ((s1516 T Z₁ : Set G) * (Y' : Set G) = (Y' : Set G) * (s1516 T Z₁ : Set G)) ∧
      ⁅V₂, Y'⁆ = V₂ ∧ Y' ≤ Subgroup.normalizer (V₂ : Set G) ∧
      s1516 T Z₁ ≤ Subgroup.normalizer (V₂ : Set G) ∧ V₂ ≤ s1516 T Z₁ ∧
      (∀ n ∈ M ⊓ g1_1516 Z₁, Odd (orderOf n) → ∃ y ∈ Y', y⁻¹ * n ∈ mZ1516 Mc Z₁)) → False

end CFSG.Quasithin.E9

module

public import CFSG.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

@[expose] def Struct15121 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx1515 T Mc M Z₁ Z₂ V₁ V₂ → Lemma15117Concl T M Z₁ → Lemma15118Concl T Mc M Z₁ →
    Lemma15119Used T Mc M Z₁ V₂ → IsL1519 Mc Z₁ L → Lemma15120Concl T Mc M Z₁ L →
    ((CharTwo L ∧ IsBlock2 (g1_1516 Z₁) L ∧ (IsAltType L 5 ∨ ∃ n : ℕ, 1 < n ∧ IsLin2Type L n)) ∨
      (IsComponentOf L (g1_1516 Z₁) ∧
        (IsBender1516 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ (∃ n : ℕ, IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) ∨
          ∃ n : ℕ, IsPSp4 2 n (↥L ⧸ CFSG.pCore 2 ↥L)))) →
    (∃ B₀ : Subgroup G, B₀ ≤ mZ1516 Mc Z₁ ∧
        B₀ ≤ Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) ∧ oTwoUpper B₀ = B₀ ∧
        ∀ v ∈ V₂, (∀ b ∈ B₀, v * b = b * v) → ∀ l ∈ L, v * l = l * v) ∨
    (∀ (p : ℕ) (Y : Subgroup G), (p = 3 ∨ p = 5) → Y ≤ M ⊓ g1_1516 Z₁ →
        Y ≤ Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G) → IsPGroup p ↥Y →
        ((s1516 T Z₁ : Set G) * (Y : Set G) = (Y : Set G) * (s1516 T Z₁ : Set G)) →
        ⁅V₂, Y⁆ = V₂ → ⁅L, Y⁆ = ⊥)

end CFSG.Quasithin

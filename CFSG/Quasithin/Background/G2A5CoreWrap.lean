module

public import CFSG.Quasithin.Background.G13Two
public import CFSG.Quasithin.Background.G2A5Seven

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model CFSG.Quasithin.G1
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G]

namespace AlmostSpecialA5Core

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Core V V₁ L T H)

include hyp

theorem G24_six' {U I S W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S) :
    (∃ s : ℕ, IsSumOfNaturalSL2ModulesOver (GaloisField 2 2) s I S S
        (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ∧
      (W ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ⊓
          (rconj W g ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) =
        conjClosure V₁ L ⊔ (U ⊓ rconj U g) ∧
      S = (W ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ⊔
          (rconj W g ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g))) ∧
      ∀ x ∈ S, x ∈ W ⊔ (conjClosure V₁ L ⊔ (U ⊓ rconj U g)) ↔
        ∀ u ∈ U, ⁅u, x⁆ ∈ conjClosure V₁ L ⊔ (U ⊓ rconj U g) :=
  hyp.G24_six hU hg hgN hI hS hW theorem_G_1_3_two

theorem G24_seven' {U I S W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : S = pCoreOf 2 I) (hW : W = U ⊓ S) :
    ∃ s : ℕ, IsSumOfNaturalSL2ModulesOver (GaloisField 2 2) s I S S
        (conjClosure V₁ L ⊔ (U ⊓ rconj U g)) ∧
      Nat.card ↥U = 2 ^ (2 * s + 5) *
        (conjClosure V₁ L).relIndex (conjClosure V₁ L ⊔ (U ⊓ rconj U g)) :=
  hyp.G24_seven hU hg hgN hI hS hW theorem_G_1_3_two

end AlmostSpecialA5Core

end CFSG.Quasithin

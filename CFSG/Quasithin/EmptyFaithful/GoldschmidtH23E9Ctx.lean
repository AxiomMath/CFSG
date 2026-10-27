module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9SetD

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure E9Ctx (T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G) : Prop where
  pre : E9Pre T Mc M Z₁ Z₂ V₁ V₂
  ctx : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂
  y5 : ∃ Y' : Subgroup G, Y' ≤ M ⊓ g1_1516 Z₁ ∧ Y' ≤ Subgroup.normalizer (thompsonJ T : Set G) ∧
    IsPGroup 5 Y' ∧ ((s1516 T Z₁ : Set G) * (Y' : Set G) = (Y' : Set G) * (s1516 T Z₁ : Set G)) ∧
    ⁅V₂, Y'⁆ = V₂ ∧ Y' ≤ Subgroup.normalizer (V₂ : Set G) ∧
    s1516 T Z₁ ≤ Subgroup.normalizer (V₂ : Set G) ∧ V₂ ≤ s1516 T Z₁

theorem exists_e9Ctx {T Mc M : Subgroup G} (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (hCE : IsCE1513 T M) (h5 : Ce15Six T Mc M 5) (hE9 : HasE9 T Mc M)
    (h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M) (h14 : Lemma15114Concl T Mc M)
    (h113 : Lemma15113Four T Mc M) :
    ∃ Z₁ Z₂ V₁ V₂ : Subgroup G, E9Ctx T Mc M Z₁ Z₂ V₁ V₂ ∧ Nat.card Z₁ = 4 := by
  obtain ⟨Z₁, Z₂, V₁, V₂, hp, hc, hy, h4⟩ := exists_e9Data hq hM hCE h5 hE9 h15 h19 h14 h113
  exact ⟨Z₁, Z₂, V₁, V₂, ⟨hp, hc, hy⟩, h4⟩

end CFSG.Quasithin.E9

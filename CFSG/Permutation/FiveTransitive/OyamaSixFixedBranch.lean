module

public import CFSG.Permutation.FiveTransitive.SemiregularSylowFixedSet

public section

namespace CFSG

namespace FiveTransitive.OyamaSixFixedBranch

open MulAction

private theorem fixed_six_of_four_le
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s))
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hSfix : (fixedPoints S X).ncard = 6)
    (g : G) (hg : orderOf g = 2) (hfix : 4 ≤ (fixedBy X g).ncard) :
    (fixedBy X g).ncard = 6 := by
  classical
  obtain ⟨e, he⟩ : ∃ e : Fin 4 ↪ X, Set.range e = s := by
    let _ : Fintype s := Fintype.ofFinite _
    let e₀ : s ≃ Fin 4 := Fintype.equivFinOfCardEq
      (by simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hs)
    let e : Fin 4 ↪ X := e₀.symm.toEmbedding.trans (Function.Embedding.subtype _)
    refine ⟨e, ?_⟩
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e₀.symm i).property
    · intro hx
      refine ⟨e₀ ⟨x, hx⟩, ?_⟩
      change (e₀.symm (e₀ ⟨x, hx⟩)).val = x
      simp
  subst s
  exact (SemiregularSylowFixedSet.fixedBy_ncard_eq_of_base_le
    G X 4 h4 e S hfree g hg hfix).trans hSfix

theorem fixedPoints_zpowers_eq_fixedBy
    (G X : Type*) [Group G] [MulAction G X] (g : G) :
    fixedPoints (Subgroup.zpowers g) X = fixedBy X g := by
  ext x
  constructor
  · intro hx
    exact mem_fixedPoints.mp hx ⟨g, Subgroup.mem_zpowers g⟩
  · intro hx
    rw [mem_fixedPoints]
    intro q
    have hg : g ∈ stabilizer G x := hx
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp q.property
    change (q : G) • x = x
    rw [← hz]
    exact (stabilizer G x).zpow_mem hg z

theorem involution_fixed_zero_two_or_six
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s))
    (hfree : ∀ (q : S) (x : X), x ∉ fixedPoints S X → q • x = x → q = 1)
    (hSfix : (fixedPoints S X).ncard = 6)
    (g : G) (hg : orderOf g = 2) :
    (fixedBy X g).ncard = 0 ∨ (fixedBy X g).ncard = 2 ∨ (fixedBy X g).ncard = 6 := by
  by_cases hfix : 4 ≤ (fixedBy X g).ncard
  · exact Or.inr (Or.inr (fixed_six_of_four_le G X h4 s hs S hfree hSfix g hg hfix))
  have hcyc : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by simp only [Nat.card_zpowers, hg, pow_one])
  have hmod := (S.isPGroup'.card_modEq_card_fixedPoints X).symm.trans
    (hcyc.card_modEq_card_fixedPoints X)
  rw [fixedPoints_zpowers_eq_fixedBy, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    hSfix] at hmod
  change 6 % 2 = (fixedBy X g).ncard % 2 at hmod
  omega

end FiveTransitive.OyamaSixFixedBranch

end CFSG

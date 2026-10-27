module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Suzuki
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245

public section

namespace CFSG.QuasithinUnique.burnsideC56_P

variable {G : Type*} [Group G] [Finite G]

theorem burnsideC56_suzuki {T U : Subgroup G} (hT : IsPGroup 2 T) (hUT : U ≤ T)
    (hU4 : Nat.card U = 4) (hUexp : ∀ u ∈ U, u ^ 2 = 1)
    (hC : T ⊓ Subgroup.centralizer (U : Set G) ≤ U) : IsDihedralOrSemidihedral T := by
  by_cases hne : U = T
  · subst hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Nontrivial ↥U := Finite.one_lt_card_iff_nontrivial.mp (by rw [hU4]; norm_num)
    haveI : IsKleinFour ↥U :=
      { card_four := hU4
        exponent_two := (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg =>
          orderOf_eq_prime (Subtype.ext (by simpa using hUexp g g.2)) hg }
    refine Or.inl ⟨1, le_rfl, ?_⟩
    rw [pow_one]
    exact IsKleinFour.nonempty_mulEquiv
  · rcases suzuki_selfCentralizing_four hT hUT hU4 hUexp hC hne with ⟨k, hk, he⟩ | ⟨n, hn, he⟩
    · exact Or.inl ⟨k, by omega, he⟩
    · exact Or.inr ⟨n, hn, he⟩

end CFSG.QuasithinUnique.burnsideC56_P

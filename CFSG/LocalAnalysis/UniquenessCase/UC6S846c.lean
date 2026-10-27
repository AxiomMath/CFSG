module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6S846

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_card_of_le_pRank {M : Subgroup G} {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : k ≤ Open.pRank p M) :
    ∃ A : Subgroup G, A ≤ M ∧ IsElemAbelian p A ∧ Nat.card A = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEM, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp M
  have hdvd : p ^ k ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow p hk
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  refine ⟨K.map E.subtype, (Subgroup.map_subtype_le K).trans hEM,
    hEel.mono (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hK]

theorem exists_card_p_sq {A : Subgroup G} {p : ℕ} (hp : p.Prime) (hA : IsElemAbelian p A)
    (hcard : p ^ 2 ≤ Nat.card A) :
    ∃ A₂ : Subgroup G, A₂ ≤ A ∧ IsElemAbelian p A₂ ∧ Nat.card A₂ = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := (hA.isPGroup).exists_card_eq
  have hj2 : 2 ≤ j := by
    by_contra h
    have : j ≤ 1 := by omega
    have : p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos this
    have h2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hdvd : p ^ 2 ∣ Nat.card A := by
    rw [hj]
    exact pow_dvd_pow p hj2
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  refine ⟨K.map A.subtype, Subgroup.map_subtype_le K, hA.mono (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hK]

end CFSG.LocalAnalysis.UniquenessCase.UC6S846

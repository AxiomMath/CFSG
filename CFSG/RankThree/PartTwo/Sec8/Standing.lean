module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven

variable {G : Type*} [Group G] [Finite G]

theorem pRank_le_localRank {H : Subgroup G} (hH : IsTwoLocal H) :
    CFSG.Assembly.pRank 3 H ≤ localRank 3 G := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨H, hH, rfl⟩
  rintro _ ⟨K, -, rfl⟩
  exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card 3 Nat.prime_three K).trans
    (Subgroup.card_le_card_group K)

theorem odd_card_of_le_normalizer (h3 : localRank 3 G ≤ 3) {E X : Subgroup G}
    (hE : IsElemAbelian 3 E) (hE81 : Nat.card E = 81) (hX : ¬ 3 ∣ Nat.card X)
    (hEX : E ≤ Subgroup.normalizer (X : Set G)) : Odd (Nat.card X) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card X := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : E →* MulAut X := X.normalizerMonoidHom.comp (Subgroup.inclusion hEX)
  let : MulDistribMulAction E X := MulDistribMulAction.compHom X φ
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  have hcard : ¬ 3 ∣ Nat.card (Sylow 2 X) := fun h => hX (h.trans
    ((Sylow.card_dvd_index (Classical.arbitrary (Sylow 2 X))).trans (Subgroup.index_dvd_card _)))
  obtain ⟨S, hS⟩ := hEp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 X) hcard
  have hSinv : ∀ e : E, ∀ s ∈ (S : Subgroup X), e • s ∈ (S : Subgroup X) := by
    intro e s hs
    have hmem : e • s ∈ ((e • S : Sylow 2 X) : Subgroup X) := by
      rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      exact ⟨s, hs, rfl⟩
    rwa [hS e] at hmem
  set T := (S : Subgroup X).map X.subtype
  have hT1 : T ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]
    exact Sylow.ne_bot_of_dvd_card S h2
  have hT2 : IsPGroup 2 T := S.isPGroup'.map X.subtype
  have hconj : ∀ e ∈ E, ∀ t ∈ T, e * t * e⁻¹ ∈ T := by
    rintro e he _ ⟨s, hs, rfl⟩
    exact ⟨_, hSinv ⟨e, he⟩ s hs, rfl⟩
  have hET : E ≤ Subgroup.normalizer (T : Set G) := fun e he => by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · exact hconj e he t
    · intro ht
      have := hconj e⁻¹ (E.inv_mem he) _ ht
      simpa [mul_assoc] using this
  have hloc : IsTwoLocal (Subgroup.normalizer (T : Set G)) := ⟨T, hT1, hT2, rfl⟩
  have hrank : 4 ≤ CFSG.Assembly.pRank 3 (Subgroup.normalizer (T : Set G)) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨E, hET, hE, by rw [hE81]; norm_num⟩
  have := pRank_le_localRank hloc
  omega

end CFSG.RankThree.PartTwo.Sec8

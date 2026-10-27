module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331ClGL
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRankAux
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.Assembly.LowTwoRank TauCeti
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls (statedClassical_of_lieModel)

theorem k331c_two_ne_zero {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : f ≠ 0) (hK : Nat.card K = p ^ f) : (2 : K) ≠ 0 := by
  intro h
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have h1 : p ∣ 2 ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self p hf
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))

theorem k331c_pRank_three_psl_two_le_one {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 3 ≤ f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) ≤ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h7 : 7 ≤ Nat.card K := by
    rw [hK]
    exact (Nat.pow_le_pow_right (by norm_num) hf).trans' (by norm_num)
  have hcyc := CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card K hK h7 3
    (by norm_num) (by rw [hK]; exact Nat.Coprime.pow_right f (by norm_num))
  refine CFSG.SectionRank.pRank_le (by norm_num) fun A _ hA => ?_
  rw [pow_one]
  exact CFSG.AGLEmbedding.card_le_of_isElemAbelian_of_isCyclic_sylow default (hcyc default) hA

theorem k331Idx_A_odd {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid) (hr : r ≤ 4)
    (hp : q.p ≠ 2) : K331Idx (.lie ⟨.A r q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩
  have hmodel : StatedClassicalModel L .PSL (r + 1) q.p q.exponent :=
    statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_A r q hv e)
  obtain ⟨⟨hpp, hf, -⟩, K, _, _, hK, ⟨eK⟩⟩ := hmodel
  exact k331At_of_proj (k331c_two_ne_zero hpp hp (by omega) hK)
    (by rw [Fintype.card_fin]; omega) eK

theorem k331Idx_twistedA_odd {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedA r q).Valid)
    (hr : r ≤ 4) (hp : q.p ≠ 2) : K331Idx (.lie ⟨.twistedA r q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA r q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA r q
  have hmodel : StatedClassicalModel L .PSU (r + 1) q.p q.exponent := by
    have := statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_twistedA r q hv e)
    rwa [hc, hf] at this
  obtain ⟨⟨hpp, hf1, -⟩, K, _, _, hK, ⟨eK⟩⟩ := hmodel
  refine k331At_of_proj (k331c_two_ne_zero hpp hp (f := q.exponent * 2) (by omega) ?_)
    (by rw [Fintype.card_fin]; omega) eK
  rw [hK, pow_mul]

theorem k331Idx_B_two {q : PrimePower} (hv : (LieTypeIndex.B 2 q).Valid) (hp : q.p ≠ 2) :
    K331Idx (.lie ⟨.B 2 q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩
  rcases CFSG.Models.lieModel_B 2 q hv e with hm | hm
  · obtain ⟨⟨hpp, hf, -⟩, K, _, _, hK, ⟨eK⟩⟩ := statedClassical_of_lieModel (by omega) hm
    exact k331At_of_proj (k331c_two_ne_zero hpp hp (by omega) hK)
      (by rw [Fintype.card_sum, Fintype.card_fin]; omega) eK
  · obtain ⟨⟨-, -, hn, -⟩, -⟩ := statedClassical_of_lieModel (by omega) hm
    omega

theorem k331Idx_A_one_even {q : PrimePower} (hv : (LieTypeIndex.A 1 q).Valid) (hp : q.p = 2) :
    K331Idx (.lie ⟨.A 1 q, hv⟩) := by
  intro L _ _ _ h3 ⟨e⟩
  have hmodel : StatedClassicalModel L .PSL (1 + 1) q.p q.exponent :=
    statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_A 1 q hv e)
  by_cases hf3 : 3 ≤ q.exponent
  · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
    rw [hp] at hK
    have eK' : L ≃* StatedProj (StatedSL 2 K) := eK
    have h1 := k331c_pRank_three_psl_two_le_one hK hf3
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3)
      (eK'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm), h3] at h1
    omega
  · obtain ⟨-, hf, -, hne, -⟩ := hmodel.1
    have hf2 : q.exponent = 2 := by
      by_contra hne2
      have h1 : q.exponent = 1 := by omega
      exact hne (by simp [hp, h1])
    rw [hp, hf2] at hmodel
    exact k331At_of_card (Or.inl (by
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_four hmodel]
      norm_num))

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

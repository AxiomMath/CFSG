module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Agl418Lower
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankClsIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven TauCeti
open CFSG.LieType.SeitzGeneration (Cat RankLE2 not_rankLE2_orthogonal_three
  exists_isElemAbelian_card_of_not_rankLE2)
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls (statedClassical_of_lieModel
  not_three_dvd_pow)
open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank (psl_three_le_pRank_of_dvd
  psu_three_le_pRank_of_dvd)

section Helpers

theorem three_le_pRank_of_char_three {S : Type} [Group S] [Finite S] {t : StatedLieTag}
    {n f : ℕ} (h : StatedClassicalModel S t n 3 f) (hn : 4 ≤ n) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨-, -, hc⟩ := CFSG.SectionRank.classical_model_rank (by norm_num : (3 : ℕ) ≠ 2) h
  rcases hc with ⟨-, ⟨h2, -⟩ | ⟨h2, -⟩ | h4⟩ | ⟨-, ⟨h2, -⟩ | h4⟩ | ⟨-, ⟨h2, -⟩ | h4⟩ | h4 <;>
    omega

private theorem three_le_pRank_of_not_rankLE2 {K : Type} [Group K] [Finite K] (h : ¬ RankLE2 3 K) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨-, E, hE, hc⟩ := exists_isElemAbelian_card_of_not_rankLE2 Nat.prime_three h
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc

theorem three_le_pRank_of_equiv {S G : Type} [Group S] [Finite S] [Group G] [Finite G]
    (e : S ≃* G) (h : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e]

theorem psl_three_le_pRank_of_six_le {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 6 ≤ n) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n K))) :=
  three_le_pRank_three_of_rotGL ((Fin.castLE_injective hn).comp finSumFinEquiv.injective)
    fun _ => Subgroup.subset_closure (det_rotMatrix _ _)

theorem psp_three_le_pRank_of_three_le {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSp n K))) :=
  three_le_pRank_three_of_rotGL ((Fin.castLE_injective hn).sumMap (Fin.castLE_injective hn))
    fun _ => Subgroup.subset_closure (rotMatrix_inl_inr_symplectic _)

end Helpers

section Families

theorem k331Idx_A {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid) (h3 : 3 ≤ r)
    (h : 5 ≤ r ∨ q.card % 3 ≠ 2) : K331Idx (.lie ⟨.A r q, hv⟩) := by
  refine K331Idx.of_three_le fun S _ _ ⟨e⟩ => ?_
  have e' : S ≃* Cat ⟨.A r q, hv⟩ := e
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hmodel : StatedClassicalModel S .PSL (r + 1) q.p q.exponent :=
    statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_A r q hv e')
  by_cases hp3 : q.p = 3
  · rw [hp3] at hmodel
    exact three_le_pRank_of_char_three hmodel (by omega)
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
  refine three_le_pRank_of_equiv eK ?_
  rcases h with h5 | h2
  · exact psl_three_le_pRank_of_six_le (by omega)
  · have := not_three_dvd_pow (f := q.exponent) q.prime_p hp3
    exact psl_three_le_pRank_of_dvd (by rw [hK, ← hq]; omega) (by omega)

theorem k331Idx_twistedA {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedA r q).Valid)
    (h3 : 3 ≤ r) (h : q.card % 3 ≠ 1) : K331Idx (.lie ⟨.twistedA r q, hv⟩) := by
  refine K331Idx.of_three_le fun S _ _ ⟨e⟩ => ?_
  have e' : S ≃* Cat ⟨.twistedA r q, hv⟩ := e
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA r q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA r q
  have hmodel : StatedClassicalModel S .PSU (r + 1) q.p q.exponent := by
    have := statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_twistedA r q hv e')
    rwa [hc, hf] at this
  by_cases hp3 : q.p = 3
  · rw [hp3] at hmodel
    exact three_le_pRank_of_char_three hmodel (by omega)
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
  refine three_le_pRank_of_equiv eK ?_
  have := not_three_dvd_pow (f := q.exponent) q.prime_p hp3
  exact psu_three_le_pRank_of_dvd (pow_pos q.prime_p.pos _).ne' hK (by omega) (by omega)

theorem k331Idx_B {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.B r q).Valid) (h3 : 3 ≤ r) :
    K331Idx (.lie ⟨.B r q, hv⟩) := by
  refine K331Idx.of_three_le fun S _ _ ⟨e⟩ => ?_
  have e' : S ≃* Cat ⟨.B r q, hv⟩ := e
  have : Finite (Cat ⟨.B r q, hv⟩) := Finite.of_equiv S e'.toEquiv
  rcases CFSG.Models.lieModel_B r q hv e' with hm | hm
  · obtain ⟨-, K, _, _, -, ⟨eK⟩⟩ := statedClassical_of_lieModel (by omega) hm
    exact three_le_pRank_of_equiv eK (psp_three_le_pRank_of_three_le h3)
  · obtain ⟨⟨-, -, hn, hp2⟩, -⟩ := statedClassical_of_lieModel (by omega) hm
    exact three_le_pRank_of_equiv e' (three_le_pRank_of_not_rankLE2
      (not_rankLE2_orthogonal_three ⟨.B r q, hv⟩ (Or.inl ⟨r, q, rfl, hn, hp2⟩)))

theorem k331Idx_C {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.C r q).Valid) :
    K331Idx (.lie ⟨.C r q, hv⟩) := by
  refine K331Idx.of_three_le fun S _ _ ⟨e⟩ => ?_
  have e' : S ≃* Cat ⟨.C r q, hv⟩ := e
  have hr : 3 ≤ r := by
    have := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
    omega
  obtain ⟨-, K, _, _, -, ⟨eK⟩⟩ := statedClassical_of_lieModel (by omega)
    (CFSG.Models.lieModel_C r q hv e')
  exact three_le_pRank_of_equiv eK (psp_three_le_pRank_of_three_le hr)

theorem k331Idx_D {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.D r q).Valid) :
    K331Idx (.lie ⟨.D r q, hv⟩) := by
  refine K331Idx.of_three_le fun S _ _ ⟨e⟩ => ?_
  have e' : S ≃* Cat ⟨.D r q, hv⟩ := e
  have : Finite (Cat ⟨.D r q, hv⟩) := Finite.of_equiv S e'.toEquiv
  exact three_le_pRank_of_equiv e' (three_le_pRank_of_not_rankLE2
    (not_rankLE2_orthogonal_three ⟨.D r q, hv⟩ (Or.inr (Or.inl ⟨r, q, rfl⟩))))

theorem k331Idx_twistedD {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedD r q).Valid) :
    K331Idx (.lie ⟨.twistedD r q, hv⟩) := by
  refine K331Idx.of_three_le fun S _ _ ⟨e⟩ => ?_
  have e' : S ≃* Cat ⟨.twistedD r q, hv⟩ := e
  have : Finite (Cat ⟨.twistedD r q, hv⟩) := Finite.of_equiv S e'.toEquiv
  exact three_le_pRank_of_equiv e' (three_le_pRank_of_not_rankLE2
    (not_rankLE2_orthogonal_three ⟨.twistedD r q, hv⟩ (Or.inr (Or.inr ⟨r, q, rfl⟩))))

theorem k331Idx_A_four_two {q : PrimePower} (hv : (LieTypeIndex.A 4 q).Valid)
    (hq2 : q.card = 2) : K331Idx (.lie ⟨.A 4 q, hv⟩) := by
  intro L _ _ _ _ ⟨e⟩ T _ K _ _
  refine Or.inr (Or.inl ?_)
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hp : q.p = 2 := by
    have h1 : q.p ∣ 2 := by
      have := dvd_pow_self q.p (Nat.pos_iff_ne_zero.1 q.exponent_pos)
      rwa [← hq, hq2] at this
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  have hf : q.exponent = 1 := by
    have h2 : 2 ^ q.exponent = 2 ^ 1 :=
      calc 2 ^ q.exponent = q.p ^ q.exponent := by rw [hp]
        _ = q.card := hq.symm
        _ = 2 ^ 1 := by rw [hq2]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  have hmodel : StatedClassicalModel L .PSL (4 + 1) q.p q.exponent :=
    statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_A 4 q hv e)
  rw [hp, hf] at hmodel
  exact Or.inl ⟨by decide, hmodel⟩

end Families

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

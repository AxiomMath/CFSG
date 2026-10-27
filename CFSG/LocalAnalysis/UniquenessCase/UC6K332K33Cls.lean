module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33Inj
import CFSG.LocalAnalysis.UniquenessCase.UC22K331RankCl
import CFSG.LocalAnalysis.UniquenessCase.UC22K331RankGapU
import CFSG.RankThree.PartTwo.Sec4.RonanK432L2List
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Agl418Lower

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open TauCeti CFSG.Assembly.LowTwoRank
open CFSG.Blueprint (LieModel)
open CFSG.LieType.SeitzGeneration (Cat IsOrthogonalIndex not_rankLE2_orthogonal_three
  exists_isElemAbelian_card_of_not_rankLE2)
open CFSG.LocalAnalysis.UniquenessCase.UC22.InS3 (three_le_pRank_of_char_three
  three_le_pRank_of_equiv psl_three_le_pRank_of_six_le psp_three_le_pRank_of_three_le
  three_le_pRank_centralizer_psu_of_six_le)
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls (statedClassical_of_lieModel
  not_three_dvd_pow)
open CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank (psl_three_le_pRank_of_dvd
  psu_three_le_pRank_of_dvd)
open CFSG.Quasithin.A318P (pRank_three_le_one_linear pRank_three_le_one_unitary)

section Helpers

private theorem k33cls_three_le_pRank_of_char_three {S : Type} [Group S] [Finite S]
    {t : StatedLieTag} {n f : ℕ} (h : StatedClassicalModel S t n 3 f)
    (hn : (n = 2 ∧ 3 ≤ f) ∨ (n = 3 ∧ 2 ≤ f)) : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨-, -, hc⟩ := CFSG.SectionRank.classical_model_rank (by norm_num : (3 : ℕ) ≠ 2) h
  rcases hc with ⟨-, ⟨h2, h3⟩ | ⟨h2, h3⟩ | h3⟩ | ⟨-, ⟨h2, h3⟩ | h3⟩ | ⟨-, ⟨h2, h3⟩ | h3⟩ | h3 <;>
    omega

private theorem k33cls_pRank_three_le_one_psl_two {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : StatedClassicalModel S .PSL 2 p f) (hp3 : p ≠ 3) (h4 : 4 ≤ p ^ f) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1 := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨eK⟩⟩ := h
  have e' : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    eK.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e']
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.pRank_psl2_le_one
    (by rw [CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp hf hK]; exact hp3)
    (by rw [hK]; exact h4)

private theorem k33cls_three_le_pRank_orthogonal {d : ValidLieTypeIndex}
    (hd : IsOrthogonalIndex d.1) {S : Type} [Group S] [Finite S] (e : S ≃* Cat d) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  have : Finite (Cat d) := Finite.of_equiv S e.toEquiv
  refine three_le_pRank_of_equiv e ?_
  obtain ⟨-, E, hE, hc⟩ := exists_isElemAbelian_card_of_not_rankLE2 Nat.prime_three
    (not_rankLE2_orthogonal_three d hd)
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc

end Helpers

section Families

theorem k33Models_A {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.A r q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  obtain ⟨hr, hdup⟩ := (LieTypeIndex.valid_iff _).mp hv
  have hr' := (LieTypeIndex.inStandardRange_iff _).mp hr
  have hdup' : ¬ ((r = 1 ∧ (q.card = 4 ∨ q.card = 5 ∨ q.card = 9)) ∨ (r = 2 ∧ q.card = 2) ∨
      (r = 3 ∧ q.card = 2)) := fun h => hdup ((LieTypeIndex.isDuplicateRepresentative_iff _).mpr h)
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hmodel : StatedClassicalModel L .PSL (r + 1) q.p q.exponent :=
    statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_A r q hv e)
  have hbp : LieModel L .PSL (r + 1) q.p q.exponent := Or.inl ⟨by decide, hmodel⟩
  by_cases hp3 : q.p = 3
  · have hc3 : q.card = 3 ^ q.exponent := by rw [hq, hp3]
    rw [hp3] at hmodel hbp
    rcases (show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with rfl | rfl | h3
    · have hf3 : 3 ≤ q.exponent := by
        by_contra hlt
        have := q.exponent_pos
        rcases (show q.exponent = 1 ∨ q.exponent = 2 by omega) with hf | hf <;>
          rw [hf] at hc3 <;> omega
      have := k33cls_three_le_pRank_of_char_three hmodel (Or.inl ⟨rfl, hf3⟩)
      omega
    · by_cases hf1 : q.exponent = 1
      · rw [hf1] at hbp
        exact K33Models.of_psl3_three_one hbp
      · have := k33cls_three_le_pRank_of_char_three hmodel
          (Or.inr ⟨rfl, by have := q.exponent_pos; omega⟩)
        omega
    · have := three_le_pRank_of_char_three hmodel (by omega)
      omega
  · have hc3 := not_three_dvd_pow (f := q.exponent) q.prime_p hp3
    rcases (show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with rfl | rfl | h3
    · have := k33cls_pRank_three_le_one_psl_two hmodel hp3 (by omega)
      omega
    · by_cases hq1 : q.card % 3 = 1
      · exact K33Models.of_psl3 (by omega) hbp
      · have := pRank_three_le_one_linear hmodel (by omega)
        omega
    · by_cases hlist : (r = 3 ∨ r = 4) ∧ q.card % 3 = 2
      · obtain ⟨hr34, hq2⟩ := hlist
        rcases hr34 with rfl | rfl
        · exact K33Models.of_psl4 (by omega) hbp
        · exact K33Models.of_psl5 (by omega) hbp
      · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
        have := three_le_pRank_of_equiv eK (by
          rcases (show 5 ≤ r ∨ 3 ∣ Nat.card K - 1 by rw [hK]; omega) with h5 | h3K
          · exact psl_three_le_pRank_of_six_le (by omega)
          · exact psl_three_le_pRank_of_dvd h3K (by omega))
        omega

theorem k33Models_twistedA {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedA r q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA r q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA r q
  have hmodel : StatedClassicalModel L .PSU (r + 1) q.p q.exponent := by
    have := statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_twistedA r q hv e)
    rwa [hc, hf] at this
  have hbp : LieModel L .PSU (r + 1) q.p q.exponent := Or.inl ⟨by decide, hmodel⟩
  by_cases hp3 : q.p = 3
  · rw [hp3] at hmodel hbp
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | h3
    · by_cases hf1 : q.exponent = 1
      · rw [hf1] at hbp
        exact K33Models.of_psu3_three_one hbp
      · have := k33cls_three_le_pRank_of_char_three hmodel
          (Or.inr ⟨rfl, by have := q.exponent_pos; omega⟩)
        omega
    · have := three_le_pRank_of_char_three hmodel (by omega)
      omega
  · have hc3 := not_three_dvd_pow (f := q.exponent) q.prime_p hp3
    by_cases hq1 : q.card % 3 = 1
    · rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with rfl | rfl | rfl | h5
      · have := pRank_three_le_one_unitary hmodel (by omega)
        omega
      · exact K33Models.of_psu4 (by omega) hbp
      · exact K33Models.of_psu5 (by omega) hbp
      · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
        obtain ⟨x, -, hx⟩ := CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank
          Nat.prime_three (H := (⊤ : Subgroup L)) (by omega)
        have hle := three_le_pRank_centralizer_psu_of_six_le hK hc3 (by omega) (by omega)
          (x := eK x) (by rw [MulEquiv.orderOf_eq]; exact hx)
        have := three_le_pRank_of_equiv eK
          (hle.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_top))
        omega
    · rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | h3
      · exact K33Models.of_psu3 (by omega) hbp
      · obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
        have := three_le_pRank_of_equiv eK (psu_three_le_pRank_of_dvd
          (pow_pos q.prime_p.pos _).ne' hK (by omega) (by omega))
        omega

theorem k33Models_B {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.B r q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have e' : L ≃* Cat ⟨.B r q, hv⟩ := e
  rcases CFSG.Models.lieModel_B r q hv e' with hm | hm
  · have hmodel := statedClassical_of_lieModel (by omega) hm
    by_cases hr2 : r = 2
    · subst hr2
      exact K33Models.of_psp4 (Or.inl ⟨by decide, hmodel⟩)
    · obtain ⟨-, K, _, _, -, ⟨eK⟩⟩ := hmodel
      have := three_le_pRank_of_equiv eK (psp_three_le_pRank_of_three_le (by omega))
      omega
  · obtain ⟨⟨-, -, hn, hp2⟩, -⟩ := statedClassical_of_lieModel (by omega) hm
    have := k33cls_three_le_pRank_orthogonal (d := ⟨.B r q, hv⟩) (Or.inl ⟨r, q, rfl, hn, hp2⟩) e'
    omega

theorem k33Models_C {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.C r q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.C r q, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨-, K, _, _, -, ⟨eK⟩⟩ := statedClassical_of_lieModel (by omega)
    (CFSG.Models.lieModel_C r q hv e)
  have := three_le_pRank_of_equiv eK (psp_three_le_pRank_of_three_le (by omega))
  omega

theorem k33Models_D {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.D r q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  have := k33cls_three_le_pRank_orthogonal (d := ⟨.D r q, hv⟩) (Or.inr (Or.inl ⟨r, q, rfl⟩)) e
  omega

theorem k33Models_twistedD {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedD r q).Valid)
    {L : Type} [Group L] [Finite L] (e : L ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  have := k33cls_three_le_pRank_orthogonal (d := ⟨.twistedD r q, hv⟩)
    (Or.inr (Or.inr ⟨r, q, rfl⟩)) e
  omega

end Families

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

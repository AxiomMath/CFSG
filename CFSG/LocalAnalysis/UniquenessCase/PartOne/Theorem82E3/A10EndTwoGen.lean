module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarGamma
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndTwoGenSeitz
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndTwoGenEven
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndTwoGenAlt
import CFSG.Adapters.LieModelOrders
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Aux
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Blueprint (LieModel)

private lemma ne_three_of_pow_mod_of_lieModel {L : Type} [Group L] {t : CFSG.Open.StatedLieTag}
    {n p f : ℕ} (hm : LieModel L t n p f) (h : p ^ f % 3 = 1 ∨ p ^ f % 3 = 2) :
    p ≠ 3 := by
  have hf : 1 ≤ f := hm.admissible.2.1
  rintro rfl
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hd : 3 ∣ 3 ^ (g + 1) := by
    rw [pow_succ]
    exact dvd_mul_left 3 _
  have h0 : 3 ^ (g + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd hd
  rcases h with h | h <;> omega

private lemma sylow_zwr_three_part {L : Type} [Group L] [Finite L] {P : Subgroup L}
    (hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) :
    81 ∣ Nat.card L ∧ ¬ 243 ∣ Nat.card L := by
  have hPcard : Nat.card P = 81 := by
    obtain ⟨eP⟩ := hPZ
    rw [Nat.card_congr eP.toEquiv]
    simpa using (UC22.InS3.UC326.zwr_card_center_Zwr (n := 1) (by norm_num)).1
  have h81 : 81 ∣ Nat.card L := by
    have hdvd := Subgroup.card_subgroup_dvd_card P
    rwa [hPcard] at hdvd
  refine ⟨h81, ?_⟩
  have hfac : (Nat.card L).factorization 3 = 4 := by
    have hP := CFSG.ABGLocalTools.IsSylowOf.card_eq hPsyl
    rw [Subgroup.card_top] at hP
    have hP' : 3 ^ (Nat.card L).factorization 3 = 3 ^ 4 := by
      rw [← hP, hPcard]
      norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ (3 : ℕ)) hP'
  intro h
  have h5 : 5 ≤ (Nat.card L).factorization 3 := by
    have h' : 3 ^ 5 ∣ Nat.card L := by
      norm_num at h ⊢
      exact h
    exact (Nat.prime_three.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mp h'
  omega

private lemma pRank_top_eq_three_of_sylow_zwr {L : Type} [Group L] [Finite L]
    {P : Subgroup L} (hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup L) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : CFSG.Open.pRank 3 P = CFSG.Open.pRank 3 (⊤ : Subgroup L) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.pRank_eq_of_isSylowOf3 Nat.prime_three hPsyl
  obtain ⟨eP⟩ := hPZ
  have h2 : CFSG.Open.pRank 3 P = 3 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup P]
    exact UC22.InS3.UC326.zwr_pRank (n := 1) le_rfl eP
  rw [← h1, h2]

private lemma glbCore_eq_top_or_of_psp_three
    {L : Type} [Group L] [Finite L] (hL : IsSimpleGroup L)
    (hnc : ∃ a b : L, a * b ≠ b * a) {A : Subgroup L}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27)
    (h81 : 81 ∣ Nat.card L) (h243 : ¬ 243 ∣ Nat.card L) {p f : ℕ}
    (hm : LieModel L .PSp 3 p f) (hp3 : p ≠ 3) :
    CFSG.Open.GLBCore 3 2 A = ⊤ ∨ LieModel L .PSp 3 2 1 := by
  by_cases hp2 : p = 2
  · have hm2 : LieModel L .PSp 3 2 f := by simpa [hp2] using hm
    rcases A10TwoGen.glbCore_eq_top_or_of_psp_two hL hnc hm2 h243 hA hcard with h | hf
    · exact Or.inl h
    · exact Or.inr (by simpa [hf] using hm2)
  · exact Or.inl (A10TwoGen.glbCore_eq_top_of_lieModel_odd hL hnc hm (by norm_num) hp2 hp3
      (fun h => by cases h) hA hcard)

private lemma glbCore_eq_top_of_pomegaMinus
    {L : Type} [Group L] [Finite L] (hL : IsSimpleGroup L)
    (hnc : ∃ a b : L, a * b ≠ b * a) {A : Subgroup L}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27)
    (h81 : 81 ∣ Nat.card L) {p f : ℕ} (hm : LieModel L .POmegaMinus 4 p f) (hp3 : p ≠ 3) :
    CFSG.Open.GLBCore 3 2 A = ⊤ := by
  by_cases hp2 : p = 2
  · have hm2 : LieModel L .POmegaMinus 4 2 f := by simpa [hp2] using hm
    exact A10TwoGen.glbCore_eq_top_of_pomegaMinus_two hL hnc hm2 hA hcard
  · exact A10TwoGen.glbCore_eq_top_of_lieModel_odd hL hnc hm (by norm_num) hp2 hp3
      (fun h => by cases h) hA hcard

private lemma glbCore_eq_top_of_pomegaOdd
    {L : Type} [Group L] [Finite L] (hL : IsSimpleGroup L)
    (hnc : ∃ a b : L, a * b ≠ b * a) {A : Subgroup L}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27)
    (h81 : 81 ∣ Nat.card L) {p f : ℕ} (hm : LieModel L .POmegaOdd 3 p f) (hp3 : p ≠ 3) :
    CFSG.Open.GLBCore 3 2 A = ⊤ := by
  have hp2 : p ≠ 2 := by
    rcases hm.admissible with ⟨-, -, h⟩
    simpa using h.2
  exact A10TwoGen.glbCore_eq_top_of_lieModel_odd hL hnc hm (by norm_num) hp2 hp3
    (fun h => by cases h) hA hcard

private lemma glbCore_eq_top_of_psl_four
    {L : Type} [Group L] [Finite L] (hL : IsSimpleGroup L)
    (hnc : ∃ a b : L, a * b ≠ b * a) {A : Subgroup L}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27)
    (h81 : 81 ∣ Nat.card L) {p f : ℕ} (hm : LieModel L .PSL 4 p f) (hq : p ^ f % 3 = 1) :
    CFSG.Open.GLBCore 3 2 A = ⊤ := by
  by_cases hp2 : p = 2
  · have hm2 : LieModel L .PSL 4 2 f := by simpa [hp2] using hm
    refine A10TwoGen.glbCore_eq_top_of_psl_two hL hnc (n := 4) (Or.inl rfl) hm2 ?_
      hA hcard
    rintro ⟨-, hf1⟩
    rw [hp2, hf1] at hq
    norm_num at hq
  · have hp3 : p ≠ 3 := ne_three_of_pow_mod_of_lieModel hm (Or.inl hq)
    exact A10TwoGen.glbCore_eq_top_of_lieModel_odd hL hnc hm (by norm_num) hp2 hp3
      (fun h => by cases h) hA hcard

private lemma glbCore_eq_top_of_psl_six_seven
    {L : Type} [Group L] [Finite L] (hL : IsSimpleGroup L)
    (hnc : ∃ a b : L, a * b ≠ b * a) {A : Subgroup L}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27)
    (h81 : 81 ∣ Nat.card L) {n p f : ℕ}
    (hm : LieModel L .PSL n p f) (hn : n = 6 ∨ n = 7) (hq : p ^ f % 3 = 2) :
    CFSG.Open.GLBCore 3 2 A = ⊤ := by
  by_cases hp2 : p = 2
  · have hm2 : LieModel L .PSL n 2 f := by simpa [hp2] using hm
    refine A10TwoGen.glbCore_eq_top_of_psl_two hL hnc (Or.inr hn) hm2 ?_ hA hcard
    rintro ⟨h4, -⟩
    omega
  · have hp3 : p ≠ 3 := ne_three_of_pow_mod_of_lieModel hm (Or.inr hq)
    exact A10TwoGen.glbCore_eq_top_of_lieModel_odd hL hnc hm (by omega) hp2 hp3
      (fun h => by cases h) hA hcard

private lemma glbCore_eq_top_of_psu_four
    {L : Type} [Group L] [Finite L] (hL : IsSimpleGroup L)
    (hnc : ∃ a b : L, a * b ≠ b * a) {A : Subgroup L}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27)
    (h81 : 81 ∣ Nat.card L) (h243 : ¬ 243 ∣ Nat.card L) {p f : ℕ}
    (hm : LieModel L .PSU 4 p f) (hq : p ^ f % 3 = 2) (hq2 : p ^ f ≠ 2) :
    CFSG.Open.GLBCore 3 2 A = ⊤ := by
  by_cases hp2 : p = 2
  · have hm2 : LieModel L .PSU 4 2 f := by simpa [hp2] using hm
    refine A10TwoGen.glbCore_eq_top_of_psu_two hL hnc (Or.inl rfl) hm2 ?_ ?_
      h243 hA hcard
    · simpa [hp2] using hq2
    · intro h4
      exact absurd rfl h4
  · have hp3 : p ≠ 3 := ne_three_of_pow_mod_of_lieModel hm (Or.inr hq)
    exact A10TwoGen.glbCore_eq_top_of_lieModel_odd hL hnc hm (by norm_num) hp2 hp3
      (fun _ => by norm_num) hA hcard

private lemma glbCore_eq_top_of_psu_six_seven
    {L : Type} [Group L] [Finite L] (hL : IsSimpleGroup L)
    (hnc : ∃ a b : L, a * b ≠ b * a) {A : Subgroup L}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27)
    (h81 : 81 ∣ Nat.card L) (h243 : ¬ 243 ∣ Nat.card L) {n p f : ℕ}
    (hm : LieModel L .PSU n p f) (hn : n = 6 ∨ n = 7) (hq : p ^ f % 3 = 1) :
    CFSG.Open.GLBCore 3 2 A = ⊤ := by
  by_cases hp2 : p = 2
  · have hm2 : LieModel L .PSU n 2 f := by simpa [hp2] using hm
    have hq1 : 2 ^ f % 3 = 1 := by simpa [hp2] using hq
    have hq2 : 2 ^ f ≠ 2 := by
      intro h
      rw [h] at hq1
      norm_num at hq1
    refine A10TwoGen.glbCore_eq_top_of_psu_two hL hnc (Or.inr hn) hm2 hq2 ?_
      h243 hA hcard
    intro h4
    omega
  · have hp3 : p ≠ 3 := ne_three_of_pow_mod_of_lieModel hm (Or.inl hq)
    exact A10TwoGen.glbCore_eq_top_of_lieModel_odd hL hnc hm (by omega) hp2 hp3
      (fun _ h => by omega) hA hcard

private lemma threeCover_false {L : Type} [Group L] (hZ : Subgroup.center L = ⊥)
    (h : CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover
      (fun Y _ => UC22.IsSpor Y .ONan) L) : False := by
  obtain ⟨-, hcenter, -⟩ := h
  rw [hZ, Subgroup.card_bot] at hcenter
  omega

private lemma alt_case {L : Type} [Group L] [Finite L] {P A : Subgroup L}
    (hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) (hAP : A ≤ P)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27)
    (e : L ≃* L ⧸ Subgroup.center L)
    (h : UC22.IsAlt (L ⧸ Subgroup.center L) 9 ∨ UC22.IsAlt (L ⧸ Subgroup.center L) 10 ∨
      UC22.IsAlt (L ⧸ Subgroup.center L) 11) :
    CFSG.Open.GLBCore 3 2 A = ⊤ ∨ UC22.IsAlt L 9 ∨ LieModel L .PSp 2 3 1 ∨
      LieModel L .PSU 4 2 1 ∨ LieModel L .PSp 3 2 1 := by
  rcases h with h9 | h10 | h11
  · obtain ⟨f9⟩ := h9
    exact Or.inr (Or.inl ⟨e.trans f9⟩)
  · obtain ⟨f10⟩ := h10
    exact Or.inl (A10TwoGen.glbCore_eq_top_of_isAlt (L := L) (n := 10) (Or.inl rfl)
      ⟨e.trans f10⟩ hPsyl hPZ hAP hA hcard)
  · obtain ⟨f11⟩ := h11
    exact Or.inl (A10TwoGen.glbCore_eq_top_of_isAlt (L := L) (n := 11) (Or.inr rfl)
      ⟨e.trans f11⟩ hPsyl hPZ hAP hA hcard)

private lemma lie_b_case {L : Type} [Group L] [Finite L] {A : Subgroup L}
    (h81 : 81 ∣ Nat.card L) (e : L ≃* L ⧸ Subgroup.center L)
    (h : LieModel (L ⧸ Subgroup.center L) .PSL 2 3 3 ∨
      LieModel (L ⧸ Subgroup.center L) .PSp 2 3 1) :
    CFSG.Open.GLBCore 3 2 A = ⊤ ∨ UC22.IsAlt L 9 ∨ LieModel L .PSp 2 3 1 ∨
      LieModel L .PSU 4 2 1 ∨ LieModel L .PSp 3 2 1 := by
  rcases h with h227 | hpsp
  · have hm : LieModel L .PSL 2 3 3 := CFSG.Blueprint.LieModel.of_mulEquiv e.symm h227
    have hcard : Nat.card L = 9828 := by
      rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num : (2 : ℕ) ≠ 0) hm]
      decide
    exact absurd (hcard ▸ h81) (by norm_num)
  · have hm : LieModel L .PSp 2 3 1 := CFSG.Blueprint.LieModel.of_mulEquiv e.symm hpsp
    exact Or.inr (Or.inr (Or.inl hm))

private lemma lie_c_case {L : Type} [Group L] [Finite L]
    (hL : IsSimpleGroup L) (hnc : ∃ a b : L, a * b ≠ b * a) {A : Subgroup L}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27)
    (h81 : 81 ∣ Nat.card L) (h243 : ¬ 243 ∣ Nat.card L)
    (e : L ≃* L ⧸ Subgroup.center L)
    (h :
      (∃ p f : ℕ, p ≠ 3 ∧ LieModel (L ⧸ Subgroup.center L) .PSp 3 p f) ∨
      (∃ p f : ℕ, p ≠ 3 ∧ LieModel (L ⧸ Subgroup.center L) .POmegaMinus 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (L ⧸ Subgroup.center L) .PSL 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ p ^ f ≠ 2 ∧
        LieModel (L ⧸ Subgroup.center L) .PSU 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel (L ⧸ Subgroup.center L) .PSL 6 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (L ⧸ Subgroup.center L) .PSU 6 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel (L ⧸ Subgroup.center L) .PSL 7 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (L ⧸ Subgroup.center L) .PSU 7 p f) ∨
      (∃ p f : ℕ, p ≠ 3 ∧ LieModel (L ⧸ Subgroup.center L) .POmegaOdd 3 p f)) :
    CFSG.Open.GLBCore 3 2 A = ⊤ ∨ UC22.IsAlt L 9 ∨ LieModel L .PSp 2 3 1 ∨
      LieModel L .PSU 4 2 1 ∨ LieModel L .PSp 3 2 1 := by
  rcases h with ⟨p, f, hp3, hm⟩ | ⟨p, f, hp3, hm⟩ | ⟨p, f, hq, hm⟩ |
    ⟨p, f, hq, hq2, hm⟩ | ⟨p, f, hq, hm⟩ | ⟨p, f, hq, hm⟩ | ⟨p, f, hq, hm⟩ |
    ⟨p, f, hq, hm⟩ | ⟨p, f, hp3, hm⟩
  · have hm' : LieModel L .PSp 3 p f := CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm
    rcases glbCore_eq_top_or_of_psp_three hL hnc hA hcard h81 h243 hm' hp3 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · have hm' : LieModel L .POmegaMinus 4 p f := CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm
    exact Or.inl (glbCore_eq_top_of_pomegaMinus hL hnc hA hcard h81 hm' hp3)
  · have hm' : LieModel L .PSL 4 p f := CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm
    exact Or.inl (glbCore_eq_top_of_psl_four hL hnc hA hcard h81 hm' hq)
  · have hm' : LieModel L .PSU 4 p f := CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm
    exact Or.inl (glbCore_eq_top_of_psu_four hL hnc hA hcard h81 h243 hm' hq hq2)
  · have hm' : LieModel L .PSL 6 p f := CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm
    exact Or.inl (glbCore_eq_top_of_psl_six_seven hL hnc hA hcard h81 hm'
      (Or.inl rfl) hq)
  · have hm' : LieModel L .PSU 6 p f := CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm
    exact Or.inl (glbCore_eq_top_of_psu_six_seven hL hnc hA hcard h81 h243 hm'
      (Or.inl rfl) hq)
  · have hm' : LieModel L .PSL 7 p f := CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm
    exact Or.inl (glbCore_eq_top_of_psl_six_seven hL hnc hA hcard h81 hm'
      (Or.inr rfl) hq)
  · have hm' : LieModel L .PSU 7 p f := CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm
    exact Or.inl (glbCore_eq_top_of_psu_six_seven hL hnc hA hcard h81 h243 hm'
      (Or.inr rfl) hq)
  · have hm' : LieModel L .POmegaOdd 3 p f := CFSG.Blueprint.LieModel.of_mulEquiv e.symm hm
    exact Or.inl (glbCore_eq_top_of_pomegaOdd hL hnc hA hcard h81 hm' hp3)

private lemma j3_case {L : Type} [Group L] [Finite L]
    {A : Subgroup L} (h243 : ¬ 243 ∣ Nat.card L)
    (e : L ≃* L ⧸ Subgroup.center L)
    (h : UC22.IsSpor (L ⧸ Subgroup.center L) .J3) :
    CFSG.Open.GLBCore 3 2 A = ⊤ ∨ UC22.IsAlt L 9 ∨ LieModel L .PSp 2 3 1 ∨
      LieModel L .PSU 4 2 1 ∨ LieModel L .PSp 3 2 1 := by
  obtain ⟨f⟩ := h
  have hcard : Nat.card L = 50232960 := by
    rw [Nat.card_congr (e.trans f).toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  exact absurd (by rw [hcard]; norm_num : 243 ∣ Nat.card L) h243

private lemma kFactE27TwoGen_at
    {L : Type}
    [Group L] [Finite L] (hZ : Subgroup.center L = ⊥) (hL : IsSimpleGroup L)
    (hnc : ∃ a b : L, a * b ≠ b * a) {P A : Subgroup L}
    (hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) (hAP : A ≤ P)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hcard : Nat.card A = 27)
    (h81 : 81 ∣ Nat.card L) (h243 : ¬ 243 ∣ Nat.card L)
    (e : L ≃* L ⧸ Subgroup.center L) (hK : Theorem82.K34odd)
    (hQ : CFSG.Open.IsQuasisimple L)
    (hcat : CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L))
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (hprank : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 3) :
    CFSG.Open.GLBCore 3 2 A = ⊤ ∨ UC22.IsAlt L 9 ∨ LieModel L .PSp 2 3 1 ∨
      LieModel L .PSU 4 2 1 ∨ LieModel L .PSp 3 2 1 := by
  rcases hK L hQ hcat hodd hprank with h3c | ⟨-, hrest⟩
  · exact (threeCover_false hZ h3c).elim
  rcases hrest with hAlt | hB | hC | hJ3
  · exact alt_case hPsyl hPZ hAP hA hcard e hAlt
  · exact lie_b_case h81 e hB
  · exact lie_c_case hL hnc hA hcard h81 h243 e hC
  · exact j3_case h243 e hJ3

theorem kFactE27TwoGen_of_k34odd (hK : Theorem82.K34odd) :
    KFactE27TwoGen := by
  intro L _ _ P A hKg hL hnc hPsyl hPZ hAP hA hcard
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hQ₀, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc
  have hQ : CFSG.Open.IsQuasisimple L :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff L).2.2.1.mp hQ₀
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hQ.2
  have hcat : CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L) :=
    CFSG.Open.IsKGroup.isCatalogGroup_of_surjective hKg ⊤ (exists_noncomm_of_isQuasisimple hQ)
      ((QuotientGroup.mk' (Subgroup.center L)).comp (⊤ : Subgroup L).subtype)
      (fun y => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) y
        exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
  have hodd : Odd (Nat.card (Subgroup.center L)) := by
    rw [hZ, Subgroup.card_bot]
    exact odd_one
  have hprank : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 3 :=
    pRank_top_eq_three_of_sylow_zwr hPsyl hPZ
  obtain ⟨h81, h243⟩ := sylow_zwr_three_part hPsyl hPZ
  let e : L ≃* L ⧸ Subgroup.center L :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.equivCenterQuot hZ
  exact kFactE27TwoGen_at hZ hL hnc hPsyl hPZ hAP hA hcard h81 h243 e hK hQ hcat hodd
    hprank

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

module

public import CFSG.LocalAnalysis.StandardType.GGExcLeviRankBase

public section

namespace CFSG.StandardType.E8LeviG3

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.Assembly CFSG.ComponentClassification.CatLeafProof
open CFSG.StandardType.F4Rest
open scoped MatrixGroups


private theorem two_le_eS_of_three_le_eP {Q r : ℕ}
    (h3 : 3 ≤ CFSG.LocalAnalysis.RankThreeUC.S15.eP Q r) :
    2 ≤ CFSG.LocalAnalysis.RankThreeUC.S15.eS Q r := by
  rw [CFSG.LocalAnalysis.RankThreeUC.S15.eS_eq_eP_div_gcd]
  set e := CFSG.LocalAnalysis.RankThreeUC.S15.eP Q r with he
  have hdiv : Nat.gcd e 2 ∣ 2 := Nat.gcd_dvd_right e 2
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (Nat.gcd e 2) hdiv with hg | hg
  · rw [hg, Nat.div_one]
    omega
  · rw [hg]
    have h2e : 2 ∣ e := hg ▸ Nat.gcd_dvd_left e 2
    obtain ⟨k, hk⟩ := h2e
    rw [hk] at h3 ⊢
    rw [Nat.mul_comm 2 k, Nat.mul_div_left k (by norm_num)]
    omega

theorem rkOmPlus_seven_le_three {Q r : ℕ}
    (h3 : 3 ≤ CFSG.LocalAnalysis.RankThreeUC.S15.eP Q r) :
    CFSG.LocalAnalysis.RankThreeUC.S15.rkOmPlus 7 Q r ≤ 3 := by
  have heS : 2 ≤ CFSG.LocalAnalysis.RankThreeUC.S15.eS Q r :=
    two_le_eS_of_three_le_eP h3
  rw [CFSG.LocalAnalysis.RankThreeUC.S15.rkOmPlus]
  split_ifs with hif
  · rw [show (2 : ℕ) * 7 = 14 from rfl]
    have hd : 14 / CFSG.LocalAnalysis.RankThreeUC.S15.eP Q r ≤ 4 := by
      have h : 14 / CFSG.LocalAnalysis.RankThreeUC.S15.eP Q r ≤ 14 / 3 :=
        Nat.div_le_div_left h3 (by norm_num : (0 : ℕ) < 3)
      norm_num at h
      exact h
    omega
  · have hd : 7 / CFSG.LocalAnalysis.RankThreeUC.S15.eS Q r ≤ 3 := by
      have h : 7 / CFSG.LocalAnalysis.RankThreeUC.S15.eS Q r ≤ 7 / 2 :=
        Nat.div_le_div_left heS (by norm_num : (0 : ℕ) < 2)
      norm_num at h
      exact h
    exact hd

theorem rkOmPlus_five_le_two {Q r : ℕ}
    (h3 : 3 ≤ CFSG.LocalAnalysis.RankThreeUC.S15.eP Q r) :
    CFSG.LocalAnalysis.RankThreeUC.S15.rkOmPlus 5 Q r ≤ 2 := by
  have heS : 2 ≤ CFSG.LocalAnalysis.RankThreeUC.S15.eS Q r :=
    two_le_eS_of_three_le_eP h3
  rw [CFSG.LocalAnalysis.RankThreeUC.S15.rkOmPlus]
  split_ifs with hif
  · rw [show (2 : ℕ) * 5 = 10 from rfl]
    have hd : 10 / CFSG.LocalAnalysis.RankThreeUC.S15.eP Q r ≤ 3 := by
      have h : 10 / CFSG.LocalAnalysis.RankThreeUC.S15.eP Q r ≤ 10 / 3 :=
        Nat.div_le_div_left h3 (by norm_num : (0 : ℕ) < 3)
      norm_num at h
      exact h
    omega
  · have hd : 5 / CFSG.LocalAnalysis.RankThreeUC.S15.eS Q r ≤ 2 := by
      have h : 5 / CFSG.LocalAnalysis.RankThreeUC.S15.eS Q r ≤ 5 / 2 :=
        Nat.div_le_div_left heS (by norm_num : (0 : ℕ) < 2)
      norm_num at h
      exact h
    exact hd

theorem card_le_pow_rkOmPlus_subsystemGroup_e8D {l : ℕ} (hl : 4 ≤ l)
    (ι : Fin l → Fin Tag.E8.rank)
    (hadj : ∀ i j : Fin l, Timmesfeld.edgeD l i j →
      ι i ≠ ι j ∧ Tag.cartan .E8 (ι i) (ι j) = -1 ∧ Tag.cartan .E8 (ι j) (ι i) = -1 ∧
        ∃ k, ¬ (3 : ℤ) ∣ Tag.cartan .E8 (ι i) k + 2 * Tag.cartan .E8 (ι j) k)
    (hnadj : ∀ i j : Fin l, i ≠ j → ¬ Timmesfeld.edgeD l i j → ¬ Timmesfeld.edgeD l j i →
      ι i ≠ ι j ∧ Tag.cartan .E8 (ι i) (ι j) = 0 ∧ Tag.cartan .E8 (ι j) (ι i) = 0)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range ι)) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ CFSG.LocalAnalysis.RankThreeUC.S15.rkOmPlus l (Nat.card K) p := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by rw [← Fintype.card_eq_nat_card]; exact hK
  have hn : 1 ≤ (n : ℕ) := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hKn
  obtain ⟨O, C, hE'⟩ := exists_e8_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE' rfl ι hadj hnadj
  have hadm : StatedLieAdmissible .POmegaPlus l 2 (n : ℕ) := ⟨Nat.prime_two, hn, hl⟩
  have hl3 : 3 ≤ l := by omega
  obtain ⟨Ψ, hker, hrange, hqs, hmodel⟩ :=
    spinPlus_frame_subgroup (n := l) hadm hl3 hKn
      (U := fun k => CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup (ι k))
      hcomm hρ hψ
  have hqs' : CFSG.IsQuasisimple ↥Ψ.range := by
    rw [hrange]; exact hqs
  have hmodel' : LieModel (↥Ψ.range ⧸ Subgroup.center ↥Ψ.range) .POmegaPlus l 2 (n : ℕ) := by
    rw [hrange]; exact hmodel
  have hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hSCM : CFSG.Open.StatedClassicalModel
      (↥Ψ.range ⧸ Subgroup.center ↥Ψ.range) .POmegaPlus l 2 (n : ℕ) :=
    hmodel'.statedClassicalModel (by decide)
  have hqsOpen : CFSG.Open.IsQuasisimple ↥Ψ.range :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥Ψ.range).2.2.1.1 hqs'
  have hpr := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20w_pRank_pomegaPlus
    (K := ↥Ψ.range) hT hqsOpen hSCM (r := p) hp hp2
  have hS : CFSG.Open.pRank p (⊤ : Subgroup Ψ.range) ≤
      CFSG.LocalAnalysis.RankThreeUC.S15.rkOmPlus l (Nat.card K) p := by
    rw [hpr, hKn]
  have hEmap : E ≤ Ψ.range.map (adjointGroup Tag.E8 K).subtype := by
    rw [hrange, map_subtype_iSup_rankOne ι]
    exact hE
  exact card_le_pow_of_le_map_subtype hp hS hEmap hEel

theorem card_le_pow_three_subsystemGroup_e8D7 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8D7Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have h := card_le_pow_rkOmPlus_subsystemGroup_e8D (l := 7) (by norm_num) e8D7Node
    e8D7_adj e8D7_nadj hp hp2 hE hEel
  have h3' : 3 ≤ CFSG.LocalAnalysis.RankThreeUC.S15.eP (Nat.card K) p := h3
  have hle := rkOmPlus_seven_le_three (Q := Nat.card K) (r := p) h3'
  calc Nat.card E ≤ p ^ CFSG.LocalAnalysis.RankThreeUC.S15.rkOmPlus 7 (Nat.card K) p := h
    _ ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos hle

theorem card_le_pow_two_subsystemGroup_e8D5 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8D5Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have h := card_le_pow_rkOmPlus_subsystemGroup_e8D (l := 5) (by norm_num) e8D5Node
    e8D5_adj e8D5_nadj hp hp2 hE hEel
  have h3' : 3 ≤ CFSG.LocalAnalysis.RankThreeUC.S15.eP (Nat.card K) p := h3
  have hle := rkOmPlus_five_le_two (Q := Nat.card K) (r := p) h3'
  calc Nat.card E ≤ p ^ CFSG.LocalAnalysis.RankThreeUC.S15.rkOmPlus 5 (Nat.card K) p := h
    _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos hle

end CFSG.StandardType.E8LeviG3

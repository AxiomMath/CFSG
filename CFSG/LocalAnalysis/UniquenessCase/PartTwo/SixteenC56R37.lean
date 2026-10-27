module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Conj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Lin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R35
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R37A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R37B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R37T

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r37_primal (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {m : ℕ}
    (hm : Case1633 D V₀ V hV L m) {i : ℕ} (hi : i + 1 < m) {g : G}
    (h : InCalO2 (m + i) D.M V₀ V g) (hcase : V₀ = ⊥ ∨ ¬ OneFirst D.M V₀ V g) : False := by
  classical
  obtain ⟨S, hSω, hSK⟩ := exists_omegaModel_of_case1633 hm
  obtain ⟨p, hp⟩ : ∃ p, D.sig = {p} := by
    rcases hm with ⟨hc, -⟩ | ⟨hc, -⟩
    · exact ⟨5, hc.2.2⟩
    · exact ⟨3, hc.2.2⟩
  have hm2 : 2 ≤ m := by rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hH16 : Hyp16 D V₀ V := hS.setting.hyp16
  have hP : PairFacts D.M V₀ V := hH16.hyp125.pairFacts
  have hMst : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  obtain ⟨hδ, hr⟩ := r16_35_holds D h61 hext h5 V₀ V L hV hS m hm
  obtain ⟨b, hbB, hbC, hbn⟩ := exists_b_of_inCalO2 hV2 h hcase
  have hbM : b ∈ D.M := (Subgroup.mem_inf.1 hbB).2
  have hbs : b ∈ stabTil V₀ V := hMst hbM
  have hb1 : actTil V₀ V hV ⟨b, hbs⟩ ≠ 1 := fun h1 =>
    hbC ((mem_cTilde_iff hV hP.le_normalizer).2 ⟨hbM, hbs, h1⟩)
  set B : Subgroup G := conjSubgroup V g ⊓ D.M with hBdef
  have hi' : E3.mQuot (conjSubgroup V g) B ≤ m + i := by
    have h1 : E3.mQuot (conjSubgroup V g) B = E3.mQuot (conjSubgroup V g) D.M := by
      unfold E3.mQuot
      rw [hBdef, inf_comm, Subgroup.inf_relIndex_right]
    rw [h1]
    exact h.1.2.2.1
  have hBγ : B ∈ E3.gammaSet V (E3.mQuot (conjSubgroup V g) B) D.M :=
    ⟨inf_le_right, g, inf_le_left, rfl⟩
  have hBst : B ≤ stabTil V₀ V := inf_le_right.trans hMst
  have hbmem : actTil V₀ V hV ⟨b, hbs⟩ ∈ barSub V₀ V hV B := actTil_mem_barSub V₀ V hV hbB hbs
  have hA1 : barSub V₀ V hV B ≠ ⊥ := fun h0 => hb1 (Subgroup.mem_bot.1 (h0 ▸ hbmem))
  have hrk : ((2 + E3.mQuot (conjSubgroup V g) B + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V :=
    le_trans (by exact_mod_cast (by omega : 2 + E3.mQuot (conjSubgroup V g) B + mSub V₀ ≤
      2 * m + mSub V₀)) hr
  have hδ2 : ((2 + E3.mQuot (conjSubgroup V g) B : ℕ) : ℕ∞) ≤ deltaInf D.M V :=
    le_trans (by exact_mod_cast (by omega : 2 + E3.mQuot (conjSubgroup V g) B ≤ 2 * m)) hδ
  have hBcal := barSub_mem_calABar_of_gammaSet D hSg h1219 h21 h22 hH16 hrk hδ2 hBγ hA1
  have hlt : ((E3.mQuot (conjSubgroup V g) B + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : E3.mQuot (conjSubgroup V g) B + mSub V₀ <
      2 + E3.mQuot (conjSubgroup V g) B + mSub V₀)) hrk
  obtain ⟨-, hcB, hMg⟩ := sixteen_twentyThree_one D h22 hH16 hBγ
    (inf_le_left : B ≤ conjSubgroup V g) hlt
  have hfixcard := card_fixed_gt_of_mQuot_le hP.le S hSK (by omega : m + i < 2 * m) hbs hbn
  obtain ⟨e, hQ, hfixe⟩ := S.exists_fixed_line_of_mem_aSet
    (Mbar_le_normalizer_lBar hS S hSω) hBcal hbmem hb1 hfixcard
  obtain ⟨E, hEV, hEB, hEcard, hEc⟩ := exists_subgroup_of_line D h61 hext h5 hS hm S hSω hSK hp
    hBst hcB hQ hfixe
  have hEM : E ≤ conjSubgroup D.M g := fun x hx => hMg ⟨hEV hx, hEB hx⟩
  have hU : E3.mQuot V (conjSubgroup D.M g⁻¹) ≤ m + i :=
    ((oDual_iff_oFirst_inv (m + i) D.M V₀ V g).1 h.1.2).2.1
  exact h.1.1.1 (conjSubgroup_le_M_of_E hS S hSω hSK hm2 (by omega : m + i < 2 * m) hU hEV hEM hEB
    hEcard hEc)

theorem r16_37_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D) :
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV → ∀ m : ℕ,
      Case1633 D V₀ V hV L m →
        ∀ i : ℕ, i + 1 < m →
          calO2 (m + i) D.M V₀ V ⊆ calO1 (m + i) D.M V₀ V ∧
            (V₀ = ⊥ → calO2 (m + i) D.M V₀ V = ∅) := by
  intro V₀ V L hV hS m hm i hi
  have hprim : ∀ g : G, InCalO2 (m + i) D.M V₀ V g → (V₀ = ⊥ ∨ ¬ OneFirst D.M V₀ V g) → False :=
    fun g hg hc => r37_primal D hSg h1219 h21 h22 h61 hext h5 hS hm hi hg hc
  refine ⟨fun X ⟨g, hXg, hg⟩ => ?_, fun h0 => ?_⟩
  · refine ⟨g, hXg, hg.1, ?_, ?_⟩
    · by_cases h0 : V₀ = ⊥
      · exact (hprim g hg (Or.inl h0)).elim
      · by_contra hOne
        exact hprim g hg (Or.inr hOne)
    · by_cases h0 : V₀ = ⊥
      · exact (hprim g hg (Or.inl h0)).elim
      · by_contra hDual
        exact hprim g⁻¹ (inCalO2_inv hg)
          (Or.inr fun h' => hDual ((oneDual_iff_oneFirst_inv _ _ _ g).2 h'))
  · ext X
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨g, -, hg⟩
    exact hprim g hg (Or.inl h0)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

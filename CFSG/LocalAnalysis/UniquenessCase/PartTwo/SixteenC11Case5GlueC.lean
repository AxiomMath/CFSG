module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5GlueA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11TI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c11_case5_mbar_le_normalizer (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h5 : Case168_5 D V₀ V hV L) :
    Mbar D.M V₀ V hV ≤ normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
  have h151 : Hyp151 D V₀ V L := hc.setting.hyp151
  intro φ hφ
  obtain ⟨m, hmM, rfl⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  by_contra hne
  have hgne : (m : G) ∉ nBar D.M V₀ V hV L := by
    intro hmem
    have h1 := (s15_Infra_mem_nBar_iff h151.hyp125 hV hmM).1 hmem
    have h2 := s15_Infra_barSub_conjSubgroup V₀ V hV m.2 L
    rw [h1] at h2
    apply hne
    have hinv : (actTil V₀ V hV m)⁻¹ ∈
        normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h2.symm
    have := (normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).inv_mem hinv
    simpa using this
  have hproof : h151.isElemAbelian = hV := Subsingleton.elim _ _
  have hcomm := (s15_Kbar_commute_conj h151 (m := (1 : G)) (m' := (m : G))
    D.M.one_mem hmM (by simpa using hgne)).2
  rw [hproof] at hcomm
  have hA : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (barSub V₀ V hV (conjSubgroup L 1)) = ⊤ := by
    rw [conjSubgroup_one, ← commV_eq_commSub]
    exact s16c11_case5_commV_eq_top h5.2.2.1
  rw [hA] at hcomm
  have hB : barSub V₀ V hV (conjSubgroup L m) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun w => ?_
    simpa using (commSub_eq_bot_iff.mp hcomm) (Subgroup.mem_top w) x hx
  have hconj := s15_Infra_barSub_conjSubgroup V₀ V hV m.2 L
  rw [hB] at hconj
  have hmap : (barSub V₀ V hV L).map
      (MulAut.conj (actTil V₀ V hV m)⁻¹).toMonoidHom = ⊥ := hconj.symm
  have hinj : Function.Injective (MulAut.conj (actTil V₀ V hV m)⁻¹).toMonoidHom :=
    MulEquiv.injective _
  have hbot : barSub V₀ V hV L = ⊥ := by
    refine Subgroup.map_injective hinj ?_
    rw [hmap, Subgroup.map_bot]
  exact hc.ne_bot hbot

theorem s16c11_case5_dvd_card_mbar (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (h5 : Case168_5 D V₀ V hV L) :
    3 ^ 3 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
  obtain ⟨e⟩ := h5.1
  have hcardF : Nat.card ↥(fstarBar D.M V₀ V hV) = 3 * 3600 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    congr 1
    · rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    · exact s16c11_case5_card_natOmegaPlus h5.2.2.1
  have hle : fstarBar D.M V₀ V hV ≤ Mbar D.M V₀ V hV := by
    unfold fstarBar Fstar
    exact Subgroup.map_subtype_le _
  have hdvd : Nat.card ↥(fstarBar D.M V₀ V hV) ∣ Nat.card ↥(Mbar D.M V₀ V hV) :=
    Subgroup.card_dvd_of_le hle
  exact (show 3 ^ 3 ∣ Nat.card ↥(fstarBar D.M V₀ V hV) by rw [hcardF]; norm_num).trans hdvd

theorem s16c11_case5_gamma_dichotomy (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (hout : Out10 D V₀ V hV)
    (h5 : Case168_5 D V₀ V hV L) {A : Subgroup G} (hA : A ∈ E3.gammaSet V 0 D.T) :
    barSub V₀ V hV A = ⊥ ∨ barSub V₀ V hV A ∈ calABar 2 D.M V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hk1 : 1 ≤ D.k := TwelveShort.one_le_k D
  have hm : MBarGT D.M V₀ V 1 :=
    (h125.mBarGT_iff_lt_mBar 1).2 (lt_of_le_of_lt hk1 hout.1)
  have hr : ((1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_le_of_lt (by exact_mod_cast Nat.add_le_add_right hk1 _)
      (s16n9b_k_add_lt_rMV D hin.hSg hin.h1219 hin.hx hin.h61 hin.h127 hc.setting.hyp16)
  have hp3 : 3 ∈ D.sig := by rw [h5.2.2.2]; exact Set.mem_singleton 3
  have hrk : 2 ≤ CFSG.Open.pRank 3 D.M := by
    have h3 := hin.hSg.three_le 3 hp3
    omega
  have hγ : V₀ = ⊥ ∨ ((1 + mSub V₀ : ℕ) : ℕ∞) < gammaN 1 D.M V :=
    Or.inr (s16n9b_lt_gammaN_of_bar hc.setting.hyp16 hV Nat.prime_three (by norm_num)
      (hin.hSg.sig1_sp 3 (hin.h1219 ▸ hp3)) hrk 1 (1 + mSub V₀)
      (s16n9b_case5_good D hV hc.setting.hyp151.le h5 1 (1 + mSub V₀)))
  have h4 : Nat.card V₀ ≤ 4 := by
    have hP := h125.pairFacts
    have h1 : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hP.elemAbelian₀.isPGroup
    have h2 : 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hc.setting.hyp16.small
    omega
  have hTI : S16C11TI D V₀ V := by
    refine s16c11_tiConj_of_stronglyEmbedded D h125 (q := 3)
      (hin.hSg.sig1_sp 3 (hin.h1219 ▸ hp3)) ?_
    intro _ w hw hw0
    have hwtil : mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩) ≠ 1 := by
      intro h
      have hmem : IntMod.mk hV ⟨w, hw⟩ ∈ modNull V₀ V hV :=
        (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).1 h
      rw [mem_modNull] at hmem
      exact hw0 hmem
    obtain ⟨φ, hφL, hφ3, hφw⟩ := s16n9b_natOmegaPlus_fix h5.2.2.1 hwtil
    exact s16c11_dvd_card_cent_of_fixed_order D (Hyp125.hyp11 hin.h127 h125) h4 hV
      Nat.prime_three (by norm_num) hw hw0
      (barSub_mono V₀ V hV hc.setting.hyp151.le hφL) hφ3 hφw
  exact s16c11_barSub_gammaSet_zero_eq_bot_or_mem D hV h125 hm hr hγ
    (fun g hg _ _ => hTI g hg) hA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

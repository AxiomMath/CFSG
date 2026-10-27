module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfDef
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfStarB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfShapeB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Coprime
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5RowStA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Unique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ThinOneA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem delta15_lt_of_fix_half (D : Data G) {V L : Subgroup G} (h : Hyp151 D ⊥ V L)
    (hKW : 3 * rk ↥(wTil ⊥ V h.isElemAbelian L ⊓ fixV (lBar ⊥ V h.isElemAbelian L)) ≤
      rk ↥(wTil ⊥ V h.isElemAbelian L))
    (hγ : 3 ≤ gamma15 D.M ⊥ V h.isElemAbelian L) :
    delta15 D.M ⊥ V h.isElemAbelian L < gamma15 D.M ⊥ V h.isElemAbelian L - 1 := by
  have hV := h.isElemAbelian
  let Lb : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV L
  let U : Subgroup (Vtil ⊥ V hV) := wTil ⊥ V hV L
  have hKWU : 3 * rk ↥(U ⊓ fixV Lb) ≤ rk ↥U := hKW
  let I : Subgroup (Vtil ⊥ V hV) :=
    imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L)
  have hIleU : I ≤ U := by
    change imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ≤ wTil ⊥ V hV L
    have h := Subgroup.map_mono (f := (mkTil ⊥ V hV))
      (Subgroup.subgroupOf_mono V
        (inf_le_right : v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L ≤ wSub ⊥ V hV L))
    change imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ≤
      imgTil ⊥ V hV (wSub ⊥ V hV L) at h
    rw [wSub, imgTil_preTil] at h
    exact h
  have hIleFix : I ≤ fixV Lb := by
    have h1 : imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) ≤ fixV (barSub ⊥ V hV L) := by
      simpa only [conjSubgroup_one] using
        s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
    have h0 := Subgroup.map_mono (f := (mkTil ⊥ V hV))
      (Subgroup.subgroupOf_mono V
        (inf_le_left : v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L ≤ v1Sub D.M ⊥ V hV L))
    change I ≤ imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) at h0
    exact h0.trans (by simpa [Lb] using h1)
  have hδle : delta15 D.M ⊥ V hV L ≤ rk ↥(U ⊓ fixV Lb) := by
    have hle : I ≤ U ⊓ fixV Lb := le_inf hIleU hIleFix
    have hrk : rk ↥I = delta15 D.M ⊥ V hV L := by
      have h := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V
        (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) hV
        (inf_le_right.trans (preTil_le ⊥ V hV _))
      have hzero : (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ⊓ ⊥ = ⊥ :=
        inf_eq_right.mpr bot_le
      rw [show imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) = I from rfl,
        hzero] at h
      have hzero' : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk]
      have h' : mSub (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) = rk ↥I := by
        simpa [hzero'] using h
      rw [show delta15 D.M ⊥ V hV L =
        mSub (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) from rfl]
      exact h'.symm
    rw [← hrk]
    exact rk_mono hle
  have h151 : Hyp151 D ⊥ V L := h
  have hUrank : rk ↥U = gamma15 D.M ⊥ V hV L + delta15 D.M ⊥ V hV L := by
    have h := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V (wSub ⊥ V hV L) hV
      (preTil_le ⊥ V hV _)
    have himg : imgTil ⊥ V hV (wSub ⊥ V hV L) = U := by
      change imgTil ⊥ V hV (wSub ⊥ V hV L) = wTil ⊥ V hV L
      rw [wSub, imgTil_preTil]
    have hzero : wSub ⊥ V hV L ⊓ ⊥ = ⊥ := inf_eq_right.mpr bot_le
    rw [himg, hzero] at h
    have hW := mSub_wSub (V₀ := ⊥) (V := V) (L := L) D h151.hyp125 hV
    have hzero' : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk]
    rw [hzero', add_zero] at h
    exact h.symm.trans hW
  have h2δ : 2 * delta15 D.M ⊥ V hV L ≤ gamma15 D.M ⊥ V hV L := by
    omega
  omega

theorem s16fh_thin_rows
    {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) :
    s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∨
      s16h_H5RowA5 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∨
      s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 ∨
      s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 ∨
      s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2 ∨
      s16h_H5RowO4 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3 ∨
      (s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) ∧ commSub ⊤ L ∈ irrSet L) := by
  rcases hc.conc.2.2 with h133 | htensor | ⟨-, hsum, -⟩ | ⟨-, -, -, h135⟩
  · exact (s16h_H5_not_pgroup hc h133).elim
  · exact (s16h_H5_not_tensor hc htensor).elim
  · rcases s16h_H5_thin_sum hc hsum with hr | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
  · rcases s16h_H5_thin_one_case4 hc h135 with
      hL3 | hA5 | hS2 | hS3 | hO2 | hO3 | hSt
    · exact Or.inl hL3
    · exact Or.inr (Or.inl hA5)
    · exact Or.inr (Or.inr (Or.inl hS2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hS3)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hO2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hO3)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hSt, s16h_H5_rowSt8_irrSet hc hSt⟩)))))

theorem s16fh_delta_lt_of_component
    (hRows : K_FixHalfRows) (D : Data G) (h1217 : R1217 D) (h163 : R16_3FComp D) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t
      (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hs : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    (hγ : 4 ≤ gamma15 D.M ⊥ V h.hyp151.isElemAbelian L) :
    delta15 D.M ⊥ V h.hyp151.isElemAbelian L < gamma15 D.M ⊥ V h.hyp151.isElemAbelian L - 1 := by
  have hV := h.hyp151.isElemAbelian
  by_cases hnt : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ 2 ≤ CFSG.Open.pRank q (lBar ⊥ V hV L)
  · obtain ⟨q, hq, hq2, hr⟩ := hnt
    have hs1 : 1 < s15 D.M ⊥ V hV L := by omega
    obtain ⟨n, hn6, hn8, hLn, hsum⟩ :=
      s16fh_nonthin_alt D h163 h ⟨t, ht, ht2, ht1, htr, hW⟩ hs1 hcomp hq hq2 hr
    have h2 := s16fh_delta_le_two_of_star_sum hRows.2 D h1217 h.hyp151 hn6 hn8 hLn hsum
    omega
  · have hthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (lBar ⊥ V hV L) ≤ 1 :=
      fun q hq hq2 => not_lt.1 fun hlt => hnt ⟨q, hq, hq2, hlt⟩
    have hCfg : s16h_H5Cfg (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) t :=
      ⟨s15_Infra_vtil_sq_eq_one ⊥ V hV, ht, ht2, ht1, htr, hW, hcomp, hthin⟩
    have hrows := s16fh_thin_rows hCfg
    have hKW := hRows.1 (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV)
      (lBar ⊥ V hV L) hrows
    exact delta15_lt_of_fix_half D h.hyp151 hKW (by omega)

theorem s16fh_delta_hyp_of_not_concl
    (hRows : K_FixHalfRows) (D : Data G) (h1217 : R1217 D) (h163 : R16_3FComp D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    (hnot : ¬ Concl164 D V₀ V h.hyp151.isElemAbelian L) :
    s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L <
        gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1 := by
  intro hs2
  have hγ : 4 ≤ gamma15 D.M V₀ V h.hyp151.isElemAbelian L := by
    by_contra hlt
    exact hnot ⟨hs2, Or.inl (by omega)⟩
  by_cases h0 : V₀ = ⊥
  · subst h0
    obtain ⟨t, ht, ht2, ht1, htr, hW⟩ := hc
    rcases hW.2.2 with h133 | ⟨K, -, g, -, -, -, htens⟩ | ⟨hcomp, -⟩ |
      ⟨-, -, hcomp, -⟩
    · have hz := s16h_delta15_eq_zero_of_inf_fixV D h.hyp151.isElemAbelian rfl
        (s16c167_wTil_inf_fixV_eq_bot_of_odd h.hyp151.isElemAbelian L
          (s16h_odd_card_of_conc4_133 h133))
      omega
    · have hfix : wTil ⊥ V h.hyp151.isElemAbelian L ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L) = ⊥ := by
        rcases htens with ⟨-, htn⟩ | ⟨-, htn⟩ | ⟨-, htn⟩
        · exact s16h_commSub_inf_fixV_eq_bot_of_tensor (by norm_num) htn
        · exact s16h_commSub_inf_fixV_eq_bot_of_tensor (by norm_num) htn
        · exact s16h_commSub_inf_fixV_eq_bot_of_tensor (by norm_num) htn
      have hz := s16h_delta15_eq_zero_of_inf_fixV D h.hyp151.isElemAbelian rfl hfix
      omega
    · exact s16fh_delta_lt_of_component hRows D h1217 h163 h ht ht2 ht1 htr hW hcomp hs2 hγ
    · exact s16fh_delta_lt_of_component hRows D h1217 h163 h ht ht2 ht1 htr hW hcomp hs2 hγ
  · exact s16c34_delta_lt_gamma_of_ne_bot D h h0 hγ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

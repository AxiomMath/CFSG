module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3NineG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenNotCartan
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Case9Core
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AENineAbs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_case9_dimD1 {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L) :
    S16C11DimD1 D V₀ V hV := by
  intro E hE hET hm hle
  have h3 : 3 ≤ rk ↥E := (s1611e3_case9_mBar h hc h9).trans hm
  have h5 : 5 ≤ rkIdx (fixV E) :=
    s1611e3_nine_five_le_rkIdx h hc h9 hE.1 hE.2.2.1 h3
  have h4 : CFSG.Open.pRank 2 (Mbar D.M V₀ V hV) ≤ 4 :=
    s1611e3_nine_pRank_two_le h hc h9
  omega

theorem s1611e3_case9_dimD2 {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L) :
    S16C11DimD2 D V₀ V hV := by
  have hv1 : v1Sub D.M V₀ V hV L = V₀ := s1611e3_nine_v1Sub h9
  obtain ⟨Z, hZ, hZnorm, hZL, hZJ, hZf, -⟩ := s16t_case9_frame D h.h1217 hV hc hv1 h9
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  obtain ⟨-, hL3, hs15, hsum, -⟩ := h9
  have hL : IsPSL 3 2 1 ↥(lBar V₀ V hV L) := s16c167_isPSL_of_isL3 hL3
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV,
        Y = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs15
    exact hs15
  have hsum' : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)) ⊥ 3 := hsum
  obtain ⟨hind, hsup⟩ := s16t_case9_directSum D h.h1217 hV hc.setting.hyp151 hv1 hc.ne_bot
  have hrk0 : rk ↥(wTil V₀ V hV L) = 9 :=
    s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  have hrktop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 18 :=
    s16t_case9_rk_top D h.h1217 hV hc.setting.hyp151 hv1 hc.ne_bot hs15 hsum
  have hn2 : (conjSubs (Mbar D.M V₀ V hV) (wTil V₀ V hV L)).ncard = 2 :=
    s16n9b_case9_conjSubs_ncard hV hind hsup hrk0 hrktop
  have hempty := s16t_aSet_three_eq_empty_of_case9 (X := Mbar D.M V₀ V hV)
    (L := lBar V₀ V hV L) hW hL hsum' hcls hn2 hind hsup hZ hZnorm hZL hZJ hZf
  intro E hE hET
  change E ∈ E3.aSet 3 (Mbar D.M V₀ V hV) at hE
  rw [hempty] at hE
  exact hE

section Certified


theorem s1611e3_case9_routeF_k2 {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L)
    (hV0 : V₀ ≠ ⊥) (hk : D.k = 2) : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  exact s1611e3_case9_core_routeF_k2 h hc h9 hV0 hk

theorem s1611e3_case9_three_dvd_of_k1 {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L)
    (hV0 : V₀ ≠ ⊥) (hk : D.k = 1) : 3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V) := by
  exact s1611e3_case9_core_three_dvd_of_k1 h hc h9 hV0 hk

theorem s1611e3_normalizer_le_of_case9 {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hp7 : 7 ∈ D.sig := by
    rw [h9.2.2.2.2]
    exact Set.mem_singleton 7
  have hm3 := s1611e3_case9_mBar h hc h9
  have hDD : S16C11TI D V₀ V → normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := fun hTI =>
    s1611e3_normalizer_le_of_dimD h hc hTI hm3 (s1611e3_case9_dimD1 h hc h9)
      (s1611e3_case9_dimD2 h hc h9) hp7
  by_cases hV0 : V₀ = ⊥
  · subst hV0
    exact hDD (s1611e3_tiConj_of_bot D V)
  · have hk2 := s16c167_k_le_two D
    have hk1 := TwelveShort.one_le_k D
    by_cases hk : D.k = 2
    · exact s1611e3_case9_routeF_k2 h hc h9 hV0 hk
    · have hk' : D.k = 1 := by omega
      exact hDD (s1611e3_tiConj_of_dvd h hc.setting.hyp16 Nat.prime_three (by norm_num)
        (s16c1614_sp_three_of_k_eq_one D hk') (s1611e3_case9_three_dvd_of_k1 h hc h9 hV0 hk'))

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

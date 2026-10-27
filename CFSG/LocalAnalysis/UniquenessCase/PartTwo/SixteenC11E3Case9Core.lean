module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9Shape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9Layer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9CentB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9K1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3LiftThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteF

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s1611e3_case9_core_routeF_k2 {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L)
    (hV0 : V₀ ≠ ⊥) (hk : D.k = 2) : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hp7 : 7 ∈ D.sig := by
    rw [h9.2.2.2.2]
    exact Set.mem_singleton 7
  obtain ⟨X, hXM, hTX, hbar, π, hπ, hker⟩ := s1611e3_exists_X_lift D hV h125
  obtain ⟨E, hEn, ⟨eE⟩, hEQ⟩ := s1611e3_case9_layer h9
  haveI := hEn
  have hshape : S1611e3ShapeL3 X := s1611e3_shapeL3_of_layer π hπ hker hEQ h9.2.1 eE
  have hF : CompFactorAutInF D.k X D.T := by
    rw [hk]
    exact s1611e3_compFactorAutInF_of_shapeL3 hTX D.sylowM.isPGroup hshape
  have hfac := s16c11_barSub_factor_of_compFactor D (h.r16_10_2 h125) (h.r16_9 h125) hV hc hXM
    hTX hF
  rw [hbar] at hfac
  obtain ⟨h7card, h7exp⟩ := s1611e3_case9_mbar_seven h9
  have hcent := s1611e3_case9_cent_seven h hc h9
  exact s16c11_normalizer_le_of_factor D h.h61 hV h125 hp7 le_rfl hfac h7exp (by omega)

end Certified

theorem s1611e3_case9_mBar {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L) :
    3 ≤ mBar D.M V₀ V hV := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hQ : Subgroup.center (↥(lBar V₀ V hV L) × ↥(lBar V₀ V hV L)) = ⊥ := by
    rw [Subgroup.center_prod, center_eq_bot_of_isL3 h9.2.1]
    simp
  obtain ⟨X, -, hXM, hXcard, hXnorm, -⟩ :=
    s16c1610_center_fstar (W := Vtil V₀ V hV) (Mb := Mbar D.M V₀ V hV) (p := 7) hQ h9.1.some
  refine s1611e3_three_le_mBar_of_normal_seven h h125 hXM hXcard hXnorm ?_
  have hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) (lBar V₀ V hV L)
      (wTil V₀ V hV L) ⊥ 3 := h9.2.2.2.1
  have h9rk : rk ↥(wTil V₀ V h125.isElemAbelian L) = 9 :=
    s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat hsum)
  have hle : wTil V₀ V h125.isElemAbelian L ≤
      (⊤ : Subgroup (Vtil V₀ V h125.isElemAbelian)) := le_top
  have hrk := rk_mono hle
  rw [rk_top] at hrk
  omega

theorem s1611e3_case9_core_three_dvd_of_k1 {D : Data G} (h : S1611e3Std D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h9 : Case168_9 D V₀ V hV L) (hV0 : V₀ ≠ ⊥) (hk : D.k = 1) :
    3 ∣ Nat.card ↥(F11.CTilde D.M V₀ V) := by
  by_contra hnd
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  obtain ⟨Xbar, hXM, hX3, hXnc, hXexp, hXperm⟩ := s1611e3_case9_exists_three h hc h9
  obtain ⟨X, hXM', hXp, hXnc', hXexp', hXperm'⟩ :=
    s1611e3_case9_lift_three D hV h125 hnd hXM hX3 hXnc hXexp hXperm
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra hns
    have h2 := (Data.k_eq_two_iff D).2 hns
    omega
  have hP : ∃ X : Subgroup G, F11.InP11 D X :=
    ⟨X, inP11_of_strongly Nat.prime_three (by norm_num) hstr hXM' hXp hXexp' hXnc' hXperm'⟩
  have hm3 : 3 ≤ mBar D.M V₀ V hV := s1611e3_case9_mBar h hc h9
  have hgt : MBarGT D.M V₀ V (D.k + 1) :=
    (h125.mBarGT_iff_lt_mBar (D.k + 1)).2 (by rw [hk]; omega)
  exact h.h1211 V₀ V h125 hP hV0 hgt

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

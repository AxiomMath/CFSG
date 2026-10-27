module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenA7FourLocalCommutation
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s168e3_fifteen_eight_local
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 2)
    (hInv : A7FourBlockInvolutionBound D V₀ V L hV)
    (h154 : Hyp154 D V₀ V L) :
    E3.wClos V 0 D.M ≤ normalizer (wSub V₀ V hV L : Set G) := by
  have h125 := c.setting.hyp151.hyp125
  have hVg : ∀ g : G, conjSubgroup V g ≤ D.M →
      conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤
        normalizer (wSub V₀ V hV L : Set G) := by
    intro g hgM
    by_contra hB
    have hVle : ¬ V ≤ conjSubgroup D.M g := by
      intro hVg
      have hcomm := s168e3_fifteen_six_local c hrow hs hInv hVg hgM
      apply hB
      have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
        sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h125 hV)
      have hBV : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤
          conjSubgroup V g := E3.conjSubgroup_mono_left g hWV
      intro b hb
      have hbC : b ∈ centralizer (V : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have h1 : ⁅x, b⁆ ∈ ⁅V, conjSubgroup V g⁆ :=
          Subgroup.commutator_mem_commutator hx (hBV hb)
        rw [hcomm] at h1
        have h2 : x * b * x⁻¹ * b⁻¹ = 1 := by
          have := Subgroup.mem_bot.1 h1
          rwa [commutatorElement_def] at this
        calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
          _ = b * x := by rw [h2, one_mul]
      have hWV' : ((wSub V₀ V hV L : Subgroup G) : Set G) ⊆ (V : Set G) :=
        fun x hx => preTil_le V₀ V hV _ hx
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hWV' hbC)
    set B := conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g with hBdef
    have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
      sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h125 hV)
    have hBV : B ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g hWV
    have hBM : B ≤ D.M := hBV.trans hgM
    have hB2 : IsPGroup 2 B := (E3.isElemAbelian_conjSubgroup hV g).isPGroup.to_le hBV
    have hlt : B ⊓ normalizer (wSub V₀ V hV L : Set G) < B := by
      refine lt_of_le_of_ne inf_le_left fun heq => hB ?_
      calc B = B ⊓ normalizer (wSub V₀ V hV L : Set G) := heq.symm
        _ ≤ normalizer (wSub V₀ V hV L : Set G) := inf_le_right
    obtain ⟨E, hBE, hEB, hE1⟩ := s15_Glue_exists_hyperplane hB2 hlt
    have hEne : E ≠ B := by
      rintro rfl
      rw [E3.mQuot_self] at hE1
      exact absurd hE1 (by norm_num)
    obtain ⟨v, hvV, hEv, ⟨b, hb, hbv⟩, hvW⟩ :=
      fifteen_seven_G D c.setting.hyp151 hV c.ne hBM hB2 hEB hBE hEne
    by_cases hcase : s15 D.M V₀ V hV L = 2 ∧
        delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1
    · have hEN : E ≤ normalizer (wSub V₀ V hV L : Set G) := by
        have hle := s15_Glue_mQuot_inf_normalizer_le_one D c.setting.hyp151 hV hBM hB2 hcase.1
        have h1 := E3.mQuot_add (V := B) hBE hEB
        have h2 : E3.mQuot E (B ⊓ normalizer (wSub V₀ V hV L : Set G)) = 0 := by omega
        have h3 := (E3.mQuot_eq_zero_iff (hB2.to_le hEB) hBE).1 h2
        rw [← h3]
        exact inf_le_right
      exact hbv (s15_Eight_fix_of_s_two D h154 hV c.ne hBdef hgM hVle hcase
        (hvW hEN) (fun e he => hEv e (hBE he)) b hb)
    · exact hbv (s15_Eight_fix_of_ne D h154 hV c.ne hBdef hgM hVle hEB hE1 hcase
        hvV hEv b hb)
  exact s15_Eight_le_of_core D c.std.h1217 h154 hV c.ne hVg

private theorem s168e3_fifteen_nine_le_conj
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 2)
    (hInv : A7FourBlockInvolutionBound D V₀ V L hV)
    (h154 : Hyp154 D V₀ V L) {g : G}
    (hgM : conjSubgroup V g ≤ D.M) : V ≤ conjSubgroup D.M g := by
  by_contra hVg
  obtain ⟨m, hm, hWm⟩ := s15_Nine_exists_conj D c.std.h1217 h154 hV c.ne hVg
  refine s15_Nine_core D h154 hV c.ne (s168e3_fifteen_eight_local c hrow hs hInv h154)
    (g := g * m⁻¹) ?_ hWm
  rw [← conjSubgroup_conjSubgroup]
  have h1 := E3.conjSubgroup_mono_left m⁻¹ hgM
  rwa [s15_Tools_conjSubgroup_M D (D.M.inv_mem hm)] at h1

theorem s168e3_fifteen_nine_local
    (c : S168e3Ctx D V₀ V L hV)
    (hrow : A7Four (lBar V₀ V hV L)
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
        fixV (lBar V₀ V hV L)))
    (hs : s15 D.M V₀ V hV L = 2)
    (hInv : A7FourBlockInvolutionBound D V₀ V L hV) :
    E3.wClos V 0 D.M ≤ centralizer (V : Set G) := by
  classical
  have h154 : Hyp154 D V₀ V L := s168e3_hyp154_of_a7Four_of_s15_eq_two c hrow hs
  refine s15_Glue_wClos_zero_le hV (fun g hgM => ?_)
  have hVle : V ≤ conjSubgroup D.M g :=
    s168e3_fifteen_nine_le_conj c hrow hs hInv h154 hgM
  have hcomm : ⁅V, conjSubgroup V g⁆ = ⊥ :=
    s168e3_fifteen_six_local c hrow hs hInv hVle hgM
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : ⁅x, b⁆ ∈ ⁅V, conjSubgroup V g⁆ :=
    Subgroup.commutator_mem_commutator hx hb
  rw [hcomm] at h1
  have h2 : x * b * x⁻¹ * b⁻¹ = 1 := by
    have := Subgroup.mem_bot.1 h1
    rwa [commutatorElement_def] at this
  calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
    _ = b * x := by rw [h2, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R37
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R39B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenSetting
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem le_rk_of_case1633 (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {m : ℕ}
    (hm : Case1633 D V₀ V hV L m) : m ≤ rk ↥V := by
  obtain ⟨-, hr⟩ := r16_35_holds D h61 hext h5 V₀ V L hV hS m hm
  have hC : ¬ centralizer (((⊥ : Subgroup G) : Subgroup G) : Set G) ≤ D.M := fun h =>
    uc22br4_M_ne_top D (top_le_iff.1 fun x _ => h (by
      simp only [Subgroup.coe_bot, Set.mem_singleton_iff]
      exact Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff.1 hy]; simp))
  have h1 := rMV_le_mQuot D.M V ⊥ bot_le hC
  rw [mQuot_bot] at h1
  have h2 : ((2 * m + mSub V₀ : ℕ) : ℕ∞) ≤ (rk ↥V : ℕ∞) := hr.trans h1
  have h3 : 2 * m + mSub V₀ ≤ rk ↥V := by exact_mod_cast h2
  omega

section Certified


theorem calO2_eq_empty_top (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    (h127 : R127 D) (h38 : R16_38 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {m : ℕ} (hm : Case1633 D V₀ V hV L m) :
    calO2 m D.M V₀ V = ∅ := by
  have hm2 : 2 ≤ m := by rcases hm with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have h37 := r16_37_holds D hSg h1219 h21 h22 h61 hext h5 V₀ V L hV hS m hm 0 (by omega)
  by_cases hV₀ : V₀ = ⊥
  · exact h37.2 hV₀
  refine Set.eq_empty_iff_forall_notMem.2 fun X hX => ?_
  obtain ⟨g, hXg, hO1⟩ := h37.1 hX
  obtain ⟨-, hr⟩ := r16_35_holds D h61 hext h5 V₀ V L hV hS m hm
  have hH := (weakClosureSetting_of_hyp125 D hext h61 h127 (r1114_holds D hext h61)
    hS.setting.hyp16.hyp125 hV₀).hyp6H
  have hlt : ((mSub V₀ + m : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : mSub V₀ + m < 2 * m + mSub V₀)) hr
  have hstar : InCalOStar m D.M V₀ V g := (hH.hyp65 hV₀ hO1).inCalOStar_of_lt_rMV hlt
  have hempty := h38 V₀ V L hV hS m hm 0 (by omega)
  exact (Set.eq_empty_iff_forall_notMem.1 hempty) X ⟨g, hXg, hstar⟩

theorem calO2_eq_empty (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    (h127 : R127 D) (h38 : R16_38 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {m : ℕ} (hm : Case1633 D V₀ V hV L m) {k : ℕ} (hk : k ≤ m) :
    calO2 k D.M V₀ V = ∅ := by
  have hmrk := le_rk_of_case1633 D h61 hext h5 hS hm
  have hsub := calO2_mono_index (M := D.M) (V₀ := V₀) hV hk hmrk
  rw [calO2_eq_empty_top D hSg h1219 h21 h22 h61 hext h5 h127 h38 hS hm] at hsub
  exact Set.subset_empty_iff.1 hsub

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

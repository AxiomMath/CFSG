module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10SecABasicV
public import CFSG.Quasithin.Vol2.Ch10SecBSetup
public import CFSG.Quasithin.Vol2.Ch10SecDPerfect
public import CFSG.Quasithin.Vol2.Ch10StatementsD
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem hypE336_of (h331 : Stmt3_3_1) (h1012 : Stmt10_1_2) (h1023 : Stmt10_2_3)
    (h4413 : TmpL6_4_4_13) (h : Hyp10 G T L I) : E3.HypE336 T (fsuVM T L I) (fsuM T L) where
  hyp322 := ⟨⟨le_top, h.fsu.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.fsu.sylow.2⟩,
    SecA.fsuVM_le_T h, SecA.le_normalizer_fsuVM T L I⟩
  qtke := h.fsu.qtke
  unique := (h1012 G T L I h).2.2.2.2.1
  local_structure := by
    intro H hH hn
    have hNV := SecA.normalizer_fsuVM_eq h (SecB.fsuM_isMaxTwoLocal h331 h)
    refine ⟨by rw [hNV], ?_⟩
    have hT : QuasithinUnique.IsSylowTwoOf T H :=
      isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hH.1.1
    obtain ⟨h2c, -⟩ := h4413 G H T (H ⊓ fsuM T L) h.fsu.simple h.fsu.nonabelian h.fsu.qtke
      hH.1.2 hn hT (SecB.isUniqueMaxOver_of_isHStar h331 h hH)
    have hXV : H ⊓ fsuM T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
      inf_le_right.trans (SecA.fsuM_le_normalizer_fsuVM T L I)
    exact QuasithinUnique.le_pCoreOf_of_normalizes inf_le_left
      (le_normalizer_inf_centralizer hXV)
      (isPGroup_inf_centralizer (N := H ⊓ fsuM T L ⊓ oTwoUpper H) inf_le_left hXV
        (SecA.fsuL0_le_normalizer_fsuVM T L I) h2c
        (fun x hx ho => ⟨hx, mem_oTwoUpper_of_odd hx.1 ho⟩)
        (exists_relIndex_oTwoUpper_eq_two_pow inf_le_left) (h1023 G T L I h H hH hn).2.1)

theorem stmt10_2_13_of (h331 : Stmt3_3_1) (h1012 : Stmt10_1_2) (h1023 : Stmt10_2_3)
    (h1029 : Stmt10_2_9) (h10212 : Stmt10_2_12) (h4413 : TmpL6_4_4_13) : Stmt10_2_13 := by
  intro G _ _ T L I h
  have hV := SecA.isElemAbelian_fsuVM h
  have hVL := SecA.commutator_fsuVM_ne_bot h.fsu
  have h336 := hypE336_of h331 h1012 h1023 h4413 h
  have hm3 : 3 ≤ E3.mQuot ⁅fsuVM T L I, L⁆ ⊥ :=
    three_le_mQuot_commutator (SecA.isPGroup_fsuVM h)
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
      (SecA.perfect_L h.fsu.maximal.1) hVL
  have hr : (3 : ℕ∞) ≤ E3.rParam (fsuVM T L I) :=
    le_trans (by exact_mod_cast hm3) (h1029 G T L I h L (Or.inl rfl)).2.1
  have hn2 : ∀ H : Subgroup G, IsHStar T (fsuM T L) H → E1.nParam H ≤ 2 := by
    intro H hH
    by_cases h1 : 1 < E1.nParam H
    · exact (h1023 G T L I h H hH h1).1.le
    · exact (not_lt.mp h1).trans (by norm_num)
  have hwn : ∀ H : Subgroup G, IsHStar T (fsuM T L) H →
      E3.wParam T (fsuVM T L I) ≤ E1.nParam H := by
    intro H hH
    have hNV := SecA.normalizer_fsuVM_eq h (SecB.fsuM_isMaxTwoLocal h331 h)
    have hmin := ASInputs.min_le_nParam_of_le hV (SecA.fsuVM_ne_bot h.fsu) h336 hH
      fun x hx => hNV ▸ Subgroup.centralizer_le_normalizer _ hx.2
    rcases le_total (E3.wParam T (fsuVM T L I)) (E3.rParam (fsuVM T L I)) with hle | hle
    · rwa [min_eq_left hle] at hmin
    · rw [min_eq_right hle] at hmin
      exact absurd (hr.trans (hmin.trans (hn2 H hH))) (by norm_num)
  obtain ⟨H0, hH0⟩ := SecB.exists_isHStar h331 h
  have hw2 : E3.wParam T (fsuVM T L I) ≤ 2 := (hwn H0 hH0).trans (hn2 H0 hH0)
  rcases h10212 G T L I h with hw | ⟨hw, h3⟩ | ⟨hw, h1⟩
  · exact absurd hw (not_lt.mpr hw2)
  · exact ⟨h3, hw, fun H hH => le_antisymm (hn2 H hH) (hw ▸ hwn H hH)⟩
  · exfalso
    have h1' : 1 < E1.nParam H0 :=
      lt_of_lt_of_le (by norm_num : (1 : ℕ∞) < 2) (hw ▸ hwn H0 hH0)
    exact (h1023 G T L I h H0 hH0 h1').2.2.2 ⟨2, h1⟩

end CFSG.Quasithin.Vol2.Ch10.SecD

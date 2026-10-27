module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModuleGen
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Main
public import CFSG.Quasithin.Background.SmithD37Num
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCFourteenSixMBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem w4Lem3_6_of_w4Lem12_8
    (h128 : W4Lem12_8) : W4Lem3_6 := by
  intro W _ _ hW Y L n hLY hLn _hFstar hSU hn2 hirrY hmY
  classical
  have hLc : IsComponentOf L Y :=
    ⟨hLY, IsSubnormal.step hLY hLn (IsSubnormal.refl Y), hSU.1⟩
  have hSUq : CFSG.IsQuasisimple ↥L := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hSU.1
  have hLne : L ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L).mp (CFSG.LocalCores.isQuasisimple_nontrivial hSUq)
  have : Nontrivial W := Subgroup.nontrivial_iff.mp (nontrivial_of_lt _ _ hirrY.1)
  have hYne : Y ≠ ⊥ := by
    intro hYbot
    exact hLne (le_bot_iff.mp (hYbot ▸ hLY))
  have hbasic : IsBasicModule Y := Thm14_5.isBasicModule_of_isIrrOn hYne hirrY
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp hLn
  have hO2 : ∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal →
      IsPGroup 2 P → P = ⊥ := by
    intro P hPY hPN hP2
    have hPN' : Y ≤ Subgroup.normalizer (P : Set (MulAut W)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).mp hPN
    have hPne : fixV P ≠ ⊥ := by
      intro hbot
      have h2 := CFSG.Quasithin.SmithD37.two_le_card_fixV hW hP2
      rw [hbot, Subgroup.card_bot] at h2
      omega
    have hstab : StableUnder Y (fixV P) := fun y hy v hv =>
      CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer (hPN' hy) hv
    rcases hirrY.2.2.2 (fixV P) hstab bot_le le_top with hbot | htop
    · exact absurd hbot hPne
    · exact B1.eq_bot_of_fixV_eq_top htop
  have hH : (⨆ X ∈ conjSet L Y, X) = L := iSup_conjSet_eq_of_le_normalizer hYN
  have hfixL : fixV L = ⊥ := by
    have hstab : StableUnder Y (fixV L) := fun y hy v hv =>
      CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer (hYN hy) hv
    rcases hirrY.2.2.2 (fixV L) hstab bot_le le_top with hbot | htop
    · exact hbot
    · exact absurd (B1.eq_bot_of_fixV_eq_top htop) hLne
  have hmYlt : E3.mParam Y < 3 * n := by omega
  obtain ⟨hCN, hmeq, hirrK⟩ :=
    su3NaturalModule_of_w4 h128 hW hLY hLc hSU (by omega) hO2 hbasic
      (by rw [hH]; exact hfixL) hmYlt
  have hCne : CFSG.Quasithin.commSub (⊤ : Subgroup W) L ≠ ⊥ := by
    intro hbot
    have hlt := hirrK.2.1
    rw [hbot, bot_inf_eq] at hlt
    exact lt_irrefl _ hlt
  have hCtop : CFSG.Quasithin.commSub (⊤ : Subgroup W) L = ⊤ := by
    have hstab : StableUnder Y (CFSG.Quasithin.commSub (⊤ : Subgroup W) L) := by
      intro y hy u hu
      have hmem := CFSG.Quasithin.StabLat.mem_stabSub_commSub
        (X := L) (Y := (⊤ : Subgroup W)) (mem_stabSub.mpr fun _ => by simp) (hYN hy)
      exact (mem_stabSub.mp hmem u).2 hu
    rcases hirrY.2.2.2 (CFSG.Quasithin.commSub (⊤ : Subgroup W) L) hstab bot_le le_top with
      hbot | htop
    · exact absurd hbot hCne
    · exact htop
  have hirrL : IsIrrOn L ⊤ ⊥ := by
    have h := hirrK.2
    rw [hCtop, hfixL, inf_bot_eq] at h
    exact h
  exact su3NatModule_of_irr hW hLY hLn (by omega) hSU
    (fun U hU => hirrL.2.2.2 U hU bot_le le_top) hmYlt

theorem w4Lem3_6_holds :
    W4Lem3_6 :=
  w4Lem3_6_of_w4Lem12_8 CFSG.LocalAnalysis.WeakClosure81.w4Lem12_8_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

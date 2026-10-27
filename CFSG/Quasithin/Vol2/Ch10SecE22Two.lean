module

public import CFSG.Quasithin.Vol2.Ch10SecE21A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem stmt10_2_2_two (h1021 : Ch10.Stmt10_2_1) (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥)
    (hn3 : ¬ Ch10.Case10_1_1Three T L I) :
    oTwoUpper H = ⁅oTwoUpper H, thompsonJ T⁆ ∧
      ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G) ∧
      ∃ _ : IsMulCommutative ↥(VZ T H), IsFFModule (V := ↥(VZ T H)) (autOn H (VZ T H)) := by
  have hmp := SecB.minParabolic_of_isHStar h331 hyp hH
  obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hyp.fsu.sylow
  have hchar : CharTwo H := charTwo_of_inH hyp.fsu.qtke.2.1 S (hS ▸ hH.1)
  obtain ⟨-, hel, hW⟩ := conjClosure_isTwoReducedIn_of_charTwo hmp.isSylow hchar
    (le_refl (quasithinOmegaOneCenter T))
  have hHW : ¬ H ≤ Subgroup.centralizer (VZ T H : Set G) := by
    intro hle
    apply hZH
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (le_conjClosure _ H).trans (Subgroup.le_centralizer_iff.mp hle)
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)
  have hJO : ¬ thompsonJ T ≤ pCoreOf 2 H := by
    intro hJO
    have hJW : thompsonJ T ≤ T ⊓ Subgroup.centralizer (VZ T H : Set G) :=
      (hmp.le_pCoreOf_iff_le_centralizer hW hHW _).mp hJO
    have h1 : ⁅VZ T H, thompsonJ T⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hJW.trans inf_le_right
    have hb : baum T = baum (pCoreOf 2 H) := ((hmp.tfae_thompsonJ hW hHW).out 1 3).mp h1
    have hHS : H ≤ Subgroup.normalizer (baum T : Set G) := by
      rw [hb]
      exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans
        (normalizer_le_normalizer_baum _)
    exact hH.2.1 (hHS.trans (h1021 G T L I hyp hn3))
  have hJW : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G) := fun h =>
    hJO ((hmp.le_pCoreOf_iff_le_centralizer hW hHW _).mpr (le_inf hJT h))
  refine ⟨?_, hJW, hel.1, ?_⟩
  · rw [← twoResidual_eq_oTwoUpper]
    have hle : ⁅twoResidual H, thompsonJ T⁆ ≤ twoResidual H :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((hJT.trans hmp.isSylow.1).trans (le_normalizer_twoResidual H))
    by_contra hne
    exact hJO ((hmp.commutator_lt_iff_le_pCoreOf hJT hTJ).mp
      (lt_of_le_of_ne hle (Ne.symm hne)))
  · have h1 : ⁅VZ T H, thompsonJ T⁆ ≠ ⊥ := by
      rw [Subgroup.commutator_comm, ne_eq, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hJW
    exact hmp.isFFModule_autOn_of_not_commutator_eq_bot hW h1

theorem stmt10_2_2_three
    (he23 : E2.E23Statement) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hshape : Stmt7_0_1_shape)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I) {n : ℕ}
    (h1 : Ch10.Case10_1_1One T L I n)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) :
    Ch10.B0 T L ≤ Subgroup.normalizer (baum T : Set G) ∧
      IsSylowTwoOf (baum T) (fsuL0 T L ⊔ baum T) := by
  obtain ⟨hsyl, hbaum, -⟩ := e23_case1 he23 h37 h38 h322 hshape h3228 hyp h1 hJ
  refine ⟨?_, hsyl⟩
  set C := Subgroup.centralizer (fsuVM T L I : Set G)
  have hTpT : Ch10.T0 T L ⊔ (T ⊓ C) ≤ T := sup_le inf_le_left inf_le_left
  have hb : baum T = baum (Ch10.T0 T L ⊔ (T ⊓ C)) := baum_eq_of_le hbaum hTpT
  have hCV : T ⊓ C = (fsuL0 T L ⊔ T) ⊓ C :=
    le_antisymm (inf_le_inf_right _ le_sup_right)
      (le_inf (inf_centralizer_le_T h37 h38 hyp) inf_le_right)
  have hB0 : Ch10.B0 T L ≤ Subgroup.normalizer
      ((Ch10.T0 T L ⊔ (T ⊓ C) : Subgroup G) : Set G) := by
    intro b hb'
    have hbL0 : b ∈ fsuL0 T L ⊓ Subgroup.normalizer (Ch10.T0 T L : Set G) := oTwoUpper_le _ hb'
    have hbH : b ∈ fsuL0 T L ⊔ T := Subgroup.mem_sup_left hbL0.1
    have hbC : b ∈ Subgroup.normalizer (((fsuL0 T L ⊔ T) ⊓ C : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hbH,
        SecA.le_normalizer_centralizer (fsuL0_sup_le_normalizer T L I) hbH⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hbL0.2, hCV,
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hbC]
  rw [hb]
  exact hB0.trans (normalizer_le_normalizer_baum _)

end CFSG.Quasithin.Vol2.Ch10.SecE

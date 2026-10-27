module

public import CFSG.Quasithin.MS93.S34EDesc
import CFSG.Quasithin.MS93.S32Basic
import CFSG.Quasithin.Background.B5NonB

public section

namespace CFSG.Quasithin.MS93.S34E

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Basic

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem uq_le_inf (h : PUHyp M T L) : Uq M T L ≤ T ⊓ L :=
  le_inf ((h.Uq_le_Xq.trans (Xq_le_pCoreOf M)).trans h.pCore_le)
    (by
      show ⁅Z0q M T, L⁆ ≤ L
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((Z0q_le M T).trans h.le_normalizer))

theorem inf_desc (h : PUHyp M T L)
    (hP : ∀ C : Subgroup G, C ≤ T ⊓ L → C ≠ ⊥ → (C.subgroupOf (T ⊓ L)).Characteristic →
      ¬ M ≤ Subgroup.normalizer (C : Set G)) :
    PUHyp (L ⊔ (T ⊓ L)) (T ⊓ L) L := by
  have hsup : L ⊔ (T ⊓ L) = L := sup_eq_left.2 inf_le_right
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hTn : T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (h.le.trans h.le_normalizer)
  refine
    { le := le_sup_right
      isPGroup := h.isPGroup.to_le inf_le_left
      ne_bot := fun hbot => h.Uq_ne_bot (le_bot_iff.1 (hbot ▸ uq_le_inf h))
      noChar := fun C hC hne hch hLN => hP C hC hne hch ?_
      pCore_le := by
        rw [hsup]
        exact le_inf ((pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer).trans
          h.pCore_le) (pCoreOf_le' L)
      charTwo := by
        rw [hsup]
        exact CharTwo.of_normal h.charTwo h.L_le hLn
      L_le := le_sup_left
      le_normalizer := by
        rw [hsup]
        exact Subgroup.le_normalizer
      eq_sup := rfl
      perfect := h.perfect
      quasisimple := h.quasisimple
      rankTwo := h.rankTwo
      sqtk := B5.sqtk_of_le h.sqtk (sup_le h.L_le (inf_le_right.trans h.L_le)) }
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := by
    have hNC := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := T ⊓ L) (C.subgroupOf (T ⊓ L))
    rw [Subgroup.map_subgroupOf_eq_of_le hC] at hNC
    exact hTn.trans hNC
  rw [h.eq_sup]
  exact sup_le (le_sup_left.trans hLN) hTC

end Basic

@[expose] def S34EDescNP2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    2 < critDist (puAmalgam h.le) →
    (IsSL3U M T L ∧ ¬ IsSL3Full M T L) ∨ (IsSp4U M T L ∧ ¬ IsSp4Full M T L) →
    (∃ C : Subgroup G, C ≤ T ⊓ (L ⊔ pCoreOf 2 M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (T ⊓ (L ⊔ pCoreOf 2 M))).Characteristic ∧
      M ≤ Subgroup.normalizer (C : Set G)) →
    (∃ C : Subgroup G, C ≤ T ⊓ L ∧ C ≠ ⊥ ∧ (C.subgroupOf (T ⊓ L)).Characteristic ∧
      M ≤ Subgroup.normalizer (C : Set G)) →
    ∃ T' : Subgroup G, T' ≤ T ∧ T' ≠ T ∧ PUHyp (L ⊔ T') T' L

theorem descNP_of_descNP2 (h2 : S34EDescNP2) : S34EDescNP := by
  intro G _ _ M T L h hmin hb hc hflat
  by_cases hP : ∃ C : Subgroup G, C ≤ T ⊓ L ∧ C ≠ ⊥ ∧ (C.subgroupOf (T ⊓ L)).Characteristic ∧
      M ≤ Subgroup.normalizer (C : Set G)
  · exact h2 G M T L h hmin hb hc hflat hP
  · push Not at hP
    refine ⟨T ⊓ L, inf_le_left, fun heq => ?_, inf_desc h hP⟩
    have hlin : T ≤ L ⊔ pCoreOf 2 M := heq.symm.le.trans (inf_le_right.trans le_sup_left)
    rcases hc with ⟨hU, hF⟩ | ⟨hU, hF⟩
    · exact hF (S34D.sl3Full_of_le_sup h hU hlin)
    · exact hF (S34D.sp4Full_of_le_sup h hU hlin)

theorem desc_of_descNP2 (h2 : S34EDescNP2) : S34R.S34RDesc :=
  desc_of_descNP (descNP_of_descNP2 h2)

theorem endNL_of_descNP2 (hred : PUReduce) (h2 : S34EDescNP2) : S34D.S34DEndNL :=
  fun G _ _ M T L h hb _ => S34D.end_of_desc hred (desc_of_descNP2 h2) G M T L h hb

end CFSG.Quasithin.MS93.S34E

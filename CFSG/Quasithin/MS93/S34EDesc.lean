module

public import CFSG.Quasithin.MS93.S34DAsm

public section

namespace CFSG.Quasithin.MS93.S34E

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Basic

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem not_good_of_nonfull (h : PUHyp M T L) (hmin : PUMin M T L)
    (hc : (IsSL3U M T L ∧ ¬ IsSL3Full M T L) ∨ (IsSp4U M T L ∧ ¬ IsSp4Full M T L)) :
    ¬ (L ⊔ charCore T (T ⊓ (L ⊔ pCoreOf 2 M))) ⊓ pCoreOf 2 M ≤
      charCore T (T ⊓ (L ⊔ pCoreOf 2 M)) := by
  intro hgood
  have heq := hmin _ (charCore_le_self _ _) (charCore_characteristic _ _) hgood
  have hlin : T ≤ L ⊔ pCoreOf 2 M := (le_of_charCore_eq heq).trans inf_le_right
  rcases hc with ⟨hU, hF⟩ | ⟨hU, hF⟩
  · exact hF (S34D.sl3Full_of_le_sup h hU hlin)
  · exact hF (S34D.sp4Full_of_le_sup h hU hlin)

theorem le_normalizer_flat (h : PUHyp M T L) :
    T ≤ Subgroup.normalizer ((T ⊓ (L ⊔ pCoreOf 2 M) : Subgroup G) : Set G) :=
  le_normalizer_inf Subgroup.le_normalizer
    (h.le.trans (le_normalizer_sup h.le_normalizer (le_normalizer_pCoreOf M)))

theorem flat_desc (h : PUHyp M T L)
    (hP : ∀ C : Subgroup G, C ≤ T ⊓ (L ⊔ pCoreOf 2 M) → C ≠ ⊥ →
      (C.subgroupOf (T ⊓ (L ⊔ pCoreOf 2 M))).Characteristic →
        ¬ M ≤ Subgroup.normalizer (C : Set G)) :
    PUHyp (L ⊔ (T ⊓ (L ⊔ pCoreOf 2 M))) (T ⊓ (L ⊔ pCoreOf 2 M)) L := by
  refine S34R.puHyp_sup_of_normal h inf_le_left (le_normalizer_flat h)
    (le_inf h.pCore_le le_sup_right) fun C hC hne hch hLN => hP C hC hne hch ?_
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := by
    have hNC := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := T ⊓ (L ⊔ pCoreOf 2 M)) (C.subgroupOf (T ⊓ (L ⊔ pCoreOf 2 M)))
    rw [Subgroup.map_subgroupOf_eq_of_le hC] at hNC
    exact (le_normalizer_flat h).trans hNC
  rw [h.eq_sup]
  exact sup_le (le_sup_left.trans hLN) hTC

end Basic

@[expose] def S34EDescNP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    2 < critDist (puAmalgam h.le) →
    (IsSL3U M T L ∧ ¬ IsSL3Full M T L) ∨ (IsSp4U M T L ∧ ¬ IsSp4Full M T L) →
    (∃ C : Subgroup G, C ≤ T ⊓ (L ⊔ pCoreOf 2 M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (T ⊓ (L ⊔ pCoreOf 2 M))).Characteristic ∧
      M ≤ Subgroup.normalizer (C : Set G)) →
    ∃ T' : Subgroup G, T' ≤ T ∧ T' ≠ T ∧ PUHyp (L ⊔ T') T' L

theorem desc_of_descNP (hNP : S34EDescNP) : S34R.S34RDesc := by
  intro G _ _ M T L h hmin hb hc
  by_cases hP : ∃ C : Subgroup G, C ≤ T ⊓ (L ⊔ pCoreOf 2 M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (T ⊓ (L ⊔ pCoreOf 2 M))).Characteristic ∧
      M ≤ Subgroup.normalizer (C : Set G)
  · exact hNP G M T L h hmin hb hc hP
  · push Not at hP
    refine ⟨T ⊓ (L ⊔ pCoreOf 2 M), inf_le_left, fun heq => ?_, flat_desc h hP⟩
    have hlin : T ≤ L ⊔ pCoreOf 2 M := heq.symm.le.trans inf_le_right
    rcases hc with ⟨hU, hF⟩ | ⟨hU, hF⟩
    · exact hF (S34D.sl3Full_of_le_sup h hU hlin)
    · exact hF (S34D.sp4Full_of_le_sup h hU hlin)

end CFSG.Quasithin.MS93.S34E

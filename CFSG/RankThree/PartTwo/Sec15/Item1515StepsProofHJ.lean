module

public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step1515HJV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y → L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L →
      omegaA A ≠ {Subgroup.zpowers c} →
        CFSG.Open.pCoreOf 2 Y ≤ Subgroup.centralizer ({c} : Set G)

@[expose] noncomputable def Step1515HJEnd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y → L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L →
      omegaA A ≠ {Subgroup.zpowers c} →
        ¬ Y ≤ Subgroup.centralizer ({c} : Set G)

theorem step1515HJ_of (hV : Step1515HJV) (hEnd : Step1515HJEnd) : Step1515HJ := by
  intro G _ _ A c L h hJ Y hY hm hYL hLY
  by_contra hΩ
  have hO2 := hV G A c L h hJ Y hY hm hYL hLY hΩ
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1
  have hYc : Y ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hYL]
    exact sup_le (inf_le_right.trans hLc) hO2
  exact hEnd G A c L h hJ Y hY hm hYL hLY hΩ hYc

end CFSG.RankThree.PartTwo.Sec15

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenOuter
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineMoving
import CFSG.GroupTheory.PerfectCoreSup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem card_vzero_le_four_of_not_le_centralizer (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h86 : W3Lem86_1 G) (h126 : R126 D)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hU : UniqueMax D.M (L ⊔ D.T)) (hLV : ¬ L ≤ centralizer (V₀ : Set G)) :
    Nat.card V₀ ≤ 4 := by
  by_contra h4
  have hV₀p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup h.pairFacts.elemAbelian₀
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV₀p
  rw [hm] at h4
  have h8 : 8 ≤ Nat.card V₀ := by
    rw [hm]
    have hm3 : 3 ≤ m := by
      by_contra h
      apply h4
      have hm2 : m ≤ 2 := by omega
      calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
        _ = 4 := by norm_num
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  have hne : V₀ ≠ ⊥ := by
    rintro rfl
    simp at h8
  have hW : InCalV D.M V₀ := hyp125_inCalV h hne
  have hTI : IsTI V₀ := hyp125_isTI h hne
  have h9 : CFSG.LocalAnalysis.WeakClosure81.Hyp9 V₀ D.T := hyp9_of_hyp125 hTim hcat D h h8
  have hNV : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hW
  have hNM : L ⊔ D.T ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hle : L ⊔ D.T ≤ normalizer (V₀ : Set G) := by
    rw [hNV]
    exact hNM
  have hsubN : CFSG.Open.IsSubnormal L (L ⊔ D.T) :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hL.1 le_sup_left hNM
  have h2 : L ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) :=
    nine_fourteen_of_not_le_centralizer h9 le_sup_right hle (sup_comm ..)
      (CFSG.GroupTheory.perfectCore_sup_pCoreOf_eq le_sup_left hsubN hL.2.1).symm
      (exists_bar2_data le_sup_left hsubN hL.2.1 hL.2.2) hLV
  exact twelve_seven_one hTim hcat D h86 h126 h.2 hW hTI h8
    (uc22p22u_uniqueMax_mono D (le_inf hNM h2) inf_le_left hU)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

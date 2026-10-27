module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddCalH

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedThree)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem mem_uniqueSet_of_card_three (S : SliceCore D L D₃ Y H) {A : Subgroup G} (hAL : A ≤ L)
    (hA3 : Nat.card A = 3) : A ∈ uniqueSet D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := CFSG.AGLEmbeddingD2.exists_eq_map_conj_of_isCyclic (J := ↥L) (p := 3)
    S.isCyclic_sylow_three_L (Y₀ := D₃.subgroupOf L) (Y₁ := A.subgroupOf L)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.D₃_le).toEquiv, S.D₃_card])
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hA3])
  have heq : A = D₃.map (MulAut.conj (j : G)).toMonoidHom := by
    ext y
    constructor
    · intro hy
      have hy' : (⟨y, hAL hy⟩ : ↥L) ∈ A.subgroupOf L := hy
      rw [hj, Subgroup.mem_map] at hy'
      obtain ⟨d, hd, hdy⟩ := hy'
      exact Subgroup.mem_map.2 ⟨d, hd, by simpa [MulAut.conj_apply] using congrArg Subtype.val hdy⟩
    · intro hy
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hy
      have hd' : (⟨d, S.D₃_le hd⟩ : ↥L) ∈ D₃.subgroupOf L := hd
      have := Subgroup.mem_map_of_mem (MulAut.conj j).toMonoidHom hd'
      rw [← hj] at this
      simpa [MulAut.conj_apply] using Subgroup.mem_subgroupOf.1 this
  rw [heq]
  exact PartTwo.conj_mem_uniqueSet S.D₃_mem (S.L_le_M j.2)

theorem mem_calY9 (S : SliceCore D L D₃ Y H) : Y ∈ F09.calY9 D := by
  refine ⟨S.Y_le_M, fun h => ?_, fun A hAY hAcard =>
    S.mem_uniqueSet_of_card_three (hAY.trans S.yl) hAcard⟩
  rcases eq_top_or_exists_le_coatom H with htop | ⟨N, hN, hHN⟩
  · exact S.H_ne_top htop
  · have hmem : N ∈ calNOf Y := ⟨hN, S.Y_le_H.trans hHN⟩
    rw [h, Set.mem_singleton_iff] at hmem
    exact S.not_H_le_M (hmem ▸ hHN)

theorem exists_hyp91 (hK3 : StronglyEmbeddedThree) (hK : UCK.K332Cyc) (h82 : F08.R82 D)
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (hKF7 : KF7Use D)
    (S : SliceCore D L D₃ Y H) : ∃ E : Subgroup G, F09.Hyp91 D Y H E := by
  obtain ⟨E, hEX, hE3, -⟩ := S.exists_order_three_le_opp
  exact ⟨E, S.mem_calY9, S.mem_calH9 hK3 hK h82 hSg h614 h76 hKF7, hEX, hE3⟩

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

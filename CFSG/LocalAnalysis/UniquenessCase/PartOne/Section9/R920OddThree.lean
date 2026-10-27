module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQuot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b
public import CFSG.LocalAnalysis.UniquenessCase.UC1K31
public import CFSG.LocalAnalysis.AGLEmbeddingD2.CyclicClosure
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem q_ne_two (S : Slice D L D₃ Y H q) : q ≠ 2 := by
  have := S.gt
  omega

end Slice

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem thin_L (S : SliceCore D L D₃ Y H) : F08.Thin8 L := by
  intro p hp hp2
  rw [← pRank_bar2_eq_of_odd hp hp2]
  exact S.facts_L.thin p hp hp2

theorem pRank_three_L (S : SliceCore D L D₃ Y H) : CFSG.Open.pRank 3 L = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : CFSG.Open.pRank 3 L ≤ 1 := S.thin_L 3 Nat.prime_three (by norm_num)
  have hd : Nat.card D₃ ∣ Nat.card L := Subgroup.card_dvd_of_le S.D₃_le
  rw [S.D₃_card] at hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 hd
  have hord : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hx3 : (x : G) ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hcard : Nat.card (Subgroup.zpowers (x : G)) = 3 ^ 1 := by
    rw [Nat.card_zpowers, hord, pow_one]
  have hge : 1 ≤ CFSG.Open.pRank 3 L :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt (Subgroup.zpowers_le.2 x.2)
      (CFSG.Open.isElemAbelian_zpowers hx3) hcard
  omega

theorem isCyclic_sylow_three_L (S : SliceCore D L D₃ Y H) (T : Sylow 3 ↥L) :
    IsCyclic ↥(T : Subgroup ↥L) := by
  have hrank : CFSG.pRank 3 ↥L ≤ 1 := by
    rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three L]
    exact S.thin_L 3 Nat.prime_three (by norm_num)
  refine CFSG.LocalAnalysis.UniquenessCase.UCK.K31.isCyclic_of_isPGroup_pRank_le_one Nat.prime_three
    (by norm_num) T.isPGroup' (le_trans ?_ hrank)
  rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three,
    CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) le_top

theorem three_dvd_card_opp (S : SliceCore D L D₃ Y H) : 3 ∣ Nat.card (Opp 3 Y) := by
  obtain ⟨e⟩ := S.nonempty_bar2_opp_equiv
  have h : 3 ∣ Nat.card (Bar2 (Opp 3 Y)) := by
    rw [← Nat.card_congr e.toEquiv]
    exact S.three_dvd_card_bar2
  exact h.trans (Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective _))

theorem exists_order_three_le_opp (S : SliceCore D L D₃ Y H) :
    ∃ E : Subgroup G, E ≤ Opp 3 Y ∧ Nat.card E = 3 ∧ E ∈ uniqueSet D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Opp 3 Y)) 3 S.three_dvd_card_opp
  have hE₀card : Nat.card (Subgroup.zpowers (x : G)) = 3 := by
    rw [Nat.card_zpowers, ← Subgroup.orderOf_coe x] at *
    simpa using hx
  have hE₀X : Subgroup.zpowers (x : G) ≤ Opp 3 Y := by
    rw [Subgroup.zpowers_le]
    exact x.2
  have hE₀L : Subgroup.zpowers (x : G) ≤ L := hE₀X.trans S.opp_le_L
  obtain ⟨j, hj⟩ := CFSG.AGLEmbeddingD2.exists_eq_map_conj_of_isCyclic (J := ↥L) (p := 3)
    S.isCyclic_sylow_three_L (Y₀ := D₃.subgroupOf L) (Y₁ := (Subgroup.zpowers (x : G)).subgroupOf L)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.D₃_le).toEquiv, S.D₃_card])
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀L).toEquiv, hE₀card])
  refine ⟨Subgroup.zpowers (x : G), hE₀X, hE₀card, ?_⟩
  have heq : Subgroup.zpowers (x : G) = D₃.map (MulAut.conj (j : G)).toMonoidHom := by
    ext y
    constructor
    · intro hy
      have hy' : (⟨y, hE₀L hy⟩ : ↥L) ∈ (Subgroup.zpowers (x : G)).subgroupOf L := hy
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

end SliceCore

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

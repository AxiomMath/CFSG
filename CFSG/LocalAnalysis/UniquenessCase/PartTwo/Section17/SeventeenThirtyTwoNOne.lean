module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyTwoSevenEmbedded
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoBorelTransport
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.UC2TenNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

section Certified


theorem v0_eq_bot_of_is3D4_one
    (hRk : Inputs1719.K_3D4TwoThreeRank) (hS7 : Inputs1719.K_3D4TwoSylowSeven)
    (hB : Inputs1719.K_3D4TwoBorel) (hN7 : Inputs1719.K_3D4TwoSevenNormalizer)
    (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (hSg : UC6S846.SigmaStd D)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D) (h869 : F08.R869 D)
    (h109 : Inputs1719.UC2_10_9 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf D.M).Normal) (h3D4 : Is3D4 (Bar2 L) 1) : V₀ = ⊥ := by
  classical
  have hLM : L ≤ D.M := hL.1.le
  have hLN : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN
  have hsp7 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 D.M :=
    isStronglyPEmbedded_seven_of_is3D4 hRk hS7 hN7 D hSg h76 h614 hL hN h3D4
  have hnt : ¬ F08.Thin8 L := by
    intro hthin
    obtain ⟨E, hEL, hEel, hEcard⟩ := exists_elemAbelian_fortyNine_le_of_is3D4 hS7 h3D4
    have hpow : 7 ^ CFSG.Open.pRank 7 E = 7 ^ 2 := by
      rw [← CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_seven hEel,
        hEcard]
      norm_num
    have hrankE : CFSG.Open.pRank 7 E = 2 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 7) hpow
    have hrankL : 2 ≤ CFSG.Open.pRank 7 L := by
      have hmono : CFSG.Open.pRank 7 E ≤ CFSG.Open.pRank 7 L :=
        CFSG.SectionRank.pRank_mono (p := 7) (by norm_num) hEL
      omega
    have hle := hthin 7 Nat.prime_seven (by norm_num)
    omega
  have hU0 : UniqueMax D.M (UC22.conjClosure D.M L) :=
    uniqueMax_conjClosure_of_not_thin h869 hL hnt
  have hUL : UniqueMax D.M (L ⊔ D.T) := by
    rw [UC22.uc22p2214_conjClosure_eq_of_normal hLM hN] at hU0
    exact UC22.uc22p22u_uniqueMax_mono D le_sup_left (sup_le hLM D.sylowM.le) hU0
  have hT2 : IsPGroup 2 D.T := (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).2.1
  have hTsylM : CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  have hSylLT : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ D.T) L := by
    rw [inf_comm]
    exact CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hTsylM hLM hLN
  have hTL : D.T ≤ Inputs1719.borelQuotN L := D.sylowM.le.trans hLN
  obtain ⟨X, hXL, hXcard, hXT⟩ :=
    Inputs1719.exists_seven_order_le_normalizer_of_is3D4_bar2 (L := L) (T := D.T) hB hTL hT2
      hSylLT h3D4
  have hX7 : IsPGroup 7 X := IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  have hX1 : X ≠ ⊥ := by
    rintro rfl
    simp at hXcard
  have hXU : UC6.InU D.M X := inU_iff_mem_uniqueSet.2
    (UC22.uc22p22r_mem_uniqueSet_of_sp D Nat.prime_seven hsp7 (hXL.trans hLM) hX7 hX1)
  exact v0_eq_bot_of_uc2_10_9_of_normal h109 hV hL hLN hUL (s := 3) (p := 7) (by decide)
    Nat.prime_seven (by norm_num) hXL hXT hXcard hXU

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

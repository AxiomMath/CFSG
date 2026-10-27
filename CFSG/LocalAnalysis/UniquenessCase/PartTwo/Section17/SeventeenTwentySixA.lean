module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.GapNE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA
public import CFSG.LocalAnalysis.WeakClosure81.EightSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteenB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem normalizer_wClos_two_not_le_of_eight_seven
    (h861 : W3Lem86_1 G) {V H T : Subgroup G} {k : ℕ}
    (hV7 : Hyp7 V) (hH : IsCalH V H) (hT : IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)))
    (hW : E3.wClos V 0 T ≠ V) (hrank : k + 2 < rk ↥V) (hHE : E1.InE k H)
    (hNE : ¬ IsCalH0 V H →
      E1.InE k (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)))
    (hC : CentralizersInM V H T) (hHnotM : ¬ H ≤ Subgroup.normalizer (V : Set G)) :
    ¬ Subgroup.normalizer (E3.wClos V 2 T : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  intro hN
  have h86 : ¬ IsCalH0 V H → H =
      (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
        (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G)) :=
    fun h0 => (h861 V H T hV7 hH h0 hT hW (Or.inl hC)).1
  have heq := eight_seven hV7 hH hT hW hrank hHE hNE (Or.inl hC) h86
  have hle : H ≤ Subgroup.normalizer (V : Set G) := by
    rw [heq]
    exact sup_le inf_le_right (inf_le_right.trans hN)
  exact hHnotM hle

theorem normalizer_Wi_two_not_le (D : Data G) (V₀ V H₀ : Subgroup G) (hV : Hyp125 D V₀ V)
    (hmin : Hyp124Min D H₀) (h126 : R126 D) (h861 : W3Lem86_1 G)
    (hm : 4 < mSub V₀) (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G)
    (hNE : Gap17_26_NE D V₀ V H₀) :
    ¬ Subgroup.normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M := by
  have hV0ne : V₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, mSub, CFSG.Quasithin.rk_bot] at hm
    omega
  obtain ⟨hV0, hCU, -⟩ : InCalV0 D.M V₀ V ∧ CentralizersUnique D.M D.T ∧
      ∀ W : Subgroup G, ¬ InCalW D.M D.T W := by
    rcases hV.1 with ⟨-, hbot⟩ | h
    · exact absurd hbot hV0ne
    · exact h
  have hVel : IsElemAbelian 2 V₀ := hV0.1.2.2.2
  have hV0T : V₀ ≤ D.T := IsSylowIn.le_of_normal (TwelveShort.isSylowIn_of_le D D.sylowM.le)
    hV0.1.2.1 (Subgroup.normal_subgroupOf_iff_le_normalizer hV0.1.2.1 |>.2 hV0.1.2.2.1)
    (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hVel)
  have hVcard : Nat.card V₀ = 2 ^ mSub V₀ := by
    rw [mSub]
    exact CFSG.Quasithin.card_eq_two_pow_of_isPGroup
      (CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hVel)
  have hW : E3.wClos V₀ 0 D.T ≠ V₀ :=
    TwelveFourteen.wClos_zero_ne_self hTim hcat D hV0.1 hV0.2.2.2.1 (by
      rw [hVcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) (by omega))
  have hV7 : Hyp7 V₀ := by
    refine ⟨hVel, ?_, hV0.2.2.2.1⟩
    rw [hVcard]
    have h2m : 2 < mSub V₀ := by omega
    have : 2 ^ 2 < 2 ^ mSub V₀ := Nat.pow_lt_pow_right (by norm_num) h2m
    omega
  have hH := hmin.1
  have hNM : Subgroup.normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hV0.1
  have hTH : D.T ≤ H₀ ⊓ Subgroup.normalizer (V₀ : Set G) :=
    le_inf hH.1 (hNM ▸ D.sylowM.le)
  have hT : IsSylowIn 2 D.T (H₀ ⊓ Subgroup.normalizer (V₀ : Set G)) :=
    TwelveShort.isSylowIn_of_le D hTH
  have hcalH : IsCalH V₀ H₀ := by
    refine ⟨hV0T.trans hH.1, ?_, ?_⟩
    · exact hH.2.2
    · have hS := TwelveShort.isSylowIn_of_le D hH.1
      have hmul := Subgroup.relIndex_mul_relIndex D.T
        (H₀ ⊓ Subgroup.normalizer (V₀ : Set G)) H₀ hTH inf_le_left
      have hodd : ¬ 2 ∣ D.T.relIndex H₀ := hS.2.2
      rw [← hmul] at hodd
      exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h => hodd (Dvd.dvd.mul_left h _))
  have hk2 : D.k ≤ 2 := TwelveSeven.k_le_two D
  have hrank : D.k + 2 < rk ↥V₀ := by
    rw [← mSub]
    omega
  have hHE : E1.InE D.k H₀ := h126 H₀ hmin
  have hC : CentralizersInM V₀ H₀ D.T := by
    intro z hz hzc hz1
    rw [hNM]
    exact inf_le_right.trans (hCU z hz hzc hz1).1
  have hnotM : ¬ H₀ ≤ Subgroup.normalizer (V₀ : Set G) := by
    rw [hNM]
    exact hH.2.1
  have hmain := normalizer_wClos_two_not_le_of_eight_seven h861 hV7 hcalH hT hW hrank hHE
    (hNE hV hmin hm) hC hnotM
  rwa [hNM] at hmain

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

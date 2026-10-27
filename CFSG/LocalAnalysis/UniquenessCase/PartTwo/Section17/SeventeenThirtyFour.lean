module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def K_U3Index : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K T H : Subgroup X) (n : ℕ),
    CFSG.Open.IsSubnormal K H → ⁅K, K⁆ = K →
    CFSG.Open.IsQuasisimple (Bar2 K) → IsSU3 (Bar2 K) n →
    IsSylowIn 2 T H → K ⊔ T = H → InFSq n H

@[expose] def HbBound (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (n : ℕ) (c : Ctx17_33 D V₀ V L n),
    bBar (UC22.conjClosure D.M L) D.M V₀ V c.hyp125.isElemAbelian ≤ n

section Certified


theorem seventeen_thirtyfour (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (h869 : F08.R869 D) {V₀ V : Subgroup G} (h117 : C117 D V₀ V)
    (hSyl : UCK.U3Syl) (hKidx : K_U3Index) (hbBound : HbBound D V₀ V) :
    R17_34At D V₀ V := by
  refine ⟨?_, ?_, ?_⟩
  ·
    intro L n c
    exact hbBound L n c
  ·
    intro L n c
    have hnt : ¬ F08.Thin8 L := not_thin_of_isSU3 hSyl c.shape
    have hL1 : barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ :=
      barSub_ne_bot_of_not_thin c.hyp125 h117 c.mem_calC hnt
    have hU : UniqueMax D.M (UC22.conjClosure D.M L) :=
      uniqueMax_conjClosure_of_not_thin h869 c.mem_calC hnt
    have hb := hbBound L n c
    by_cases hV₀ : V₀ = ⊥
    · have h := twelve_twentyThree_one D hx h61 h126 h111 c.hyp125 hV₀ c.mem_calC.1
        c.mem_calC.2.2 hL1 hU
      omega
    ·
      let H : Subgroup G := L ⊔ D.T
      have hHM : H ≤ D.M := sup_le c.mem_calC.1.le D.sylowM.le
      have hUL : UniqueMax D.M L := by
        have hN : calNOf L = {D.M} :=
          h869 L (Or.inl c.mem_calC) L le_rfl
            (sup_eq_left.2 (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hnt
        exact uc22p22u_uniqueMax_of_calN D c.mem_calC.1.le hN
      have hUH : UniqueMax D.M H :=
        uc22p22u_uniqueMax_mono D le_sup_left hHM hUL
      have hsubH : CFSG.Open.IsSubnormal L H := by
        have h := c.mem_calC.1.inf H
        rwa [inf_eq_left.2 le_sup_left, inf_eq_right.2 hHM] at h
      have hIn : InFSq n H :=
        hKidx G L D.T H n hsubH c.mem_calC.2.1 c.mem_calC.2.2 c.shape
          (TwelveShort.isSylowIn_of_le D le_sup_right) rfl
      have h := twelve_twentyThree_two D hx h61 h127 h1114 h162 hTor h1482 h126 c.hyp125
        hV₀ c.mem_calC.1 c.mem_calC.2.2 hL1
        (Δ := {H})
        (by
          intro K hK
          rw [Finset.mem_singleton] at hK
          subst K
          exact ⟨le_sup_right, hHM⟩)
        (by simpa using hUH) (fun _ => n)
        (by
          intro K hK
          rw [Finset.mem_singleton] at hK
          subst K
          exact hIn)
      have hsum : ({H} : Finset (Subgroup G)).sum (fun _ => n) = n := by simp
      rw [hsum] at h
      omega
  ·
    intro L n c hV₀
    have hnt : ¬ F08.Thin8 L := not_thin_of_isSU3 hSyl c.shape
    have hL1 : barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ :=
      barSub_ne_bot_of_not_thin c.hyp125 h117 c.mem_calC hnt
    have hU : UniqueMax D.M (UC22.conjClosure D.M L) :=
      uniqueMax_conjClosure_of_not_thin h869 c.mem_calC hnt
    have h := twelve_twentyThree_one D hx h61 h126 h111 c.hyp125 hV₀ c.mem_calC.1
      c.mem_calC.2.2 hL1 hU
    have hb := hbBound L n c
    omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

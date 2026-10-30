module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p21e_s21_1_notN_of (D : Data G) (h640 : UC6.R6_40_2 D) (X : Subgroup G)
    (hY : calMOf (X ⊔ D.T) = {D.M}) : ¬ X ≤ normalizer (D.T : Set G) := by
  intro hXN
  have hcalC : UC6.calCGS D.T ≤ D.M := by
    unfold UC6.calCGS
    refine iSup_le fun C => iSup_le fun hC1 => iSup_le fun hCT => iSup_le fun hchar => ?_
    have hloc : IsTwoLocal (normalizer (C : Set G)) :=
      ⟨C, hC1, D.sylowM.isPGroup.to_le hCT, rfl⟩
    have hTC : D.T ≤ normalizer (C : Set G) :=
      Subgroup.le_normalizer.trans
        (CFSG.RankThree.PartOne.Sec15Final.normalizer_le_normalizer_of_characteristic hCT hchar)
    have hxC : X ≤ normalizer (C : Set G) := fun x hx =>
      CFSG.RankThree.PartOne.Sec15Final.normalizer_le_normalizer_of_characteristic hCT hchar (hXN hx)
    have hKC : X ⊔ D.T ≤ normalizer (C : Set G) := sup_le hxC hTC
    obtain ⟨N, hN, hge⟩ := uc22p20a_exists_max_ge hloc
    have hmem : N ∈ calMOf (X ⊔ D.T) := ⟨hN, hKC.trans hge⟩
    rw [hY] at hmem
    exact (Set.mem_singleton_iff.1 hmem) ▸ hge
  exact uc22p20a_M_ne_top D (top_le_iff.mp (h640.1 ▸ hcalC))

@[expose] def S21_1Hyp (D : Data G) (X : Subgroup G) : Prop :=
  (Nat.card X).Prime ∧ Nat.card X ≠ 2 ∧ IsSolvable ↥(X ⊔ D.T) ∧
    (∃ A : Subgroup G, IsHallOddIn A (X ⊔ D.T) ∧ IsMulCommutative A) ∧
    (∀ p ∈ piSet (X ⊔ D.T), p ≠ 2 → CFSG.Open.pRank p (X ⊔ D.T) ≤ 2) ∧ X ∈ uniqueSet D.M

@[expose] def Core211L (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx21 D Ch, ∀ X : Subgroup G, S21_1Hyp D X →
    ∀ H ∈ hSet D.T D.M, X ⊔ D.T ≤ H → ∀ L ∈ calLOf D.T D.M H, L ≤ D.M

theorem uc22p21e_core211_of_core211L (D : Data G) (Ch : Choice2011 G) (h204 : S20_4 D)
    (hL : Core211L D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) (X : Subgroup G)
    (hX : S21_1Hyp D X) : calMOf (X ⊔ D.T) = {D.M} := by
  ext H
  constructor
  · intro hH
    by_contra hne
    have hne' : H ≠ D.M := hne
    have hTH : D.T ≤ H := le_sup_right.trans hH.2
    have hHM : ¬ H ≤ D.M := fun hle => hne' (hH.1.2 D.M D.maxLocal.1 hle).symm
    have hset : H ∈ hSet D.T D.M := ⟨hTH, hHM, D.standing.charTwo H hH.1.1⟩
    have hex : ∃ L, L ∈ calLOf D.T D.M H := by
      by_contra hno
      push Not at hno
      have h := h204 h1930 H hset
      have hbot : (⨆ L ∈ calLOf D.T D.M H, L : Subgroup G) = ⊥ := by simp [hno]
      rw [hbot] at h
      apply hHM
      intro y hy
      have hy' : y ∈ (((⊥ : Subgroup G) : Set G) * ((H ⊓ D.M : Subgroup G) : Set G)) := by
        rw [h]; exact hy
      obtain ⟨a, ha, b, hb, rfl⟩ := hy'
      have ha1 : a = 1 := ha
      show a * b ∈ D.M
      rw [ha1, one_mul]
      exact hb.2
    obtain ⟨L, hLH⟩ := hex
    have hLM : L ≤ D.M := hL h1930 c X hX H hset (hH.2) L hLH
    exact hLH.1.2.2.1.2.1 (sup_le hLM D.sylowM.le)
  · rintro rfl
    exact ⟨D.maxLocal, sup_le hX.2.2.2.2.2.1 D.sylowM.le⟩

theorem uc22p21e_s21_1_of (D : Data G) (Ch : Choice2011 G) (h204 : S20_4 D) (h640 : UC6.R6_40_2 D)
    (hL : Core211L D Ch) : S21_1 D Ch := by
  intro h1930 c X hp hp2 hsol hhall hrank hU
  have hX : S21_1Hyp D X := ⟨hp, hp2, hsol, hhall, hrank, hU⟩
  have hM := uc22p21e_core211_of_core211L D Ch h204 hL h1930 c X hX
  exact ⟨hM, uc22p21e_s21_1_notN_of D h640 X hM⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

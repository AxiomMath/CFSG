module

public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAPairSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitGGroup
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s16t3_good_nat_sp {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) (x : Fin m ⊕ Fin m → K) :
    ∃ F : Subgroup ↥(StatedSp m K), IsPGroup 3 ↥F ∧ ¬ IsCyclic ↥F ∧
      ∀ γ ∈ F, ((γ : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).mulVec x = x := by
  classical
  obtain ⟨g₁, g₂, h₁, h₂, hcomm, hnot, hg₁, hg₂⟩ :=
    s16c13bcA_pairFixed_statedSp (K := K) (n := m) hm x
  have h₁3 : g₁ ^ 3 = 1 := by rw [← h₁]; exact pow_orderOf_eq_one g₁
  have h₂3 : g₂ ^ 3 = 1 := by rw [← h₂]; exact pow_orderOf_eq_one g₂
  have h₁1 : g₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h₁
    exact absurd h₁ (by norm_num)
  have h₂1 : g₂ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h₂
    exact absurd h₂ (by norm_num)
  have hba : g₂ ≠ g₁ := by
    intro h
    apply hnot
    rw [h]
    exact Subgroup.mem_zpowers g₁
  have hba2 : g₂ ≠ g₁ ^ 2 := by
    intro h
    apply hnot
    rw [h]
    exact Subgroup.mem_zpowers_iff.2 ⟨2, by simp⟩
  obtain ⟨hpg, hnc⟩ := s16c1g_closure_pair h₁3 h₂3 hcomm h₁1 h₂1 hba hba2
  have hfix : ∀ g ∈ Subgroup.closure ({g₁, g₂} : Set ↥(StatedSp m K)), g • x = x := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hg₁
      · exact hg₂
    | one => exact one_smul _ _
    | mul a b ha hb iha ihb => rw [mul_smul, ihb, iha]
    | inv a ha iha =>
      calc a⁻¹ • x = a⁻¹ • (a • x) := by rw [iha]
        _ = x := by rw [← mul_smul, inv_mul_cancel, one_smul]
  refine ⟨Subgroup.closure ({g₁, g₂} : Set ↥(StatedSp m K)), hpg, hnc, ?_⟩
  intro γ hγ
  have hmem : γ • x = x := hfix γ hγ
  simpa only [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec] using hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

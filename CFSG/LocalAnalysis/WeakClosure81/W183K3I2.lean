module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Kern
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Kern2
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Diag
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Fin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt)
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ A : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem br3_I2_member_free (_rows : Br3Rows) (h : Assumption131 Y Γ VA i)
    (hVfix : ∀ B ∈ Γ, VA B ≤ fixSub B) (hi : 2 ≤ i) (htwo : Br3TwoComp Y T L₁ L₂)
    (hshape₁ : IsL3 (↥L₁ ⧸ Subgroup.center ↥L₁) 2 ∨ IsAlt (↥L₁ ⧸ Subgroup.center ↥L₁) 6)
    (hshape₂ : IsL3 (↥L₂ ⧸ Subgroup.center ↥L₂) 2 ∨ IsAlt (↥L₂ ⧸ Subgroup.center ↥L₂) 6)
    (hA : A ∈ Γ) (h4 : 4 ≤ Nat.card ↥A)
    (hAn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hAn₂ : A ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)))
    (hm₁ : mOf A (A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ≤ 2)
    (hm₂ : mOf A (A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ≤ 2) :
    Nat.card ↥A = 4 ∧
      ((A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥ ∧
          A ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))) ∨
        (A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥ ∧
          A ≤ Subgroup.centralizer (L₁ : Set (LGL 2 V)))) := by
  classical
  have hAn₁' : ∀ a ∈ A, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := fun a ha l hl =>
    (Subgroup.mem_normalizer_iff.mp (hAn₁ ha) l).mp hl
  have hAn₂' : ∀ a ∈ A, ∀ l ∈ L₂, a * l * a⁻¹ ∈ L₂ := fun a ha l hl =>
    (Subgroup.mem_normalizer_iff.mp (hAn₂ ha) l).mp hl
  have hel : IsElemAbelian 2 A := h.isElemAb A hA
  have hAY : A ≤ Y := h.le_G A hA
  have hDF : (A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ⊓
      (A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨⟨hyA, hyC₁⟩, -, hyC₂⟩ := hy
    refine htwo.eq_one_of_isPGroup_cent (hAY hyA) (k := 1) (by simpa using hel.2 y hyA) ?_ ?_
    · intro l hl
      exact (Subgroup.mem_centralizer_iff.mp hyC₁ l hl).symm
    · intro l hl
      exact (Subgroup.mem_centralizer_iff.mp hyC₂ l hl).symm
  have hr : mRank A ≤ i := by
    by_cases hD : A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥
    · rw [hD, mOf_bot] at hm₁
      omega
    by_cases hF : A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥
    · rw [hF, mOf_bot] at hm₂
      omega
    exfalso
    exact h.false_of_two_kernels_quasi hA htwo.le₁ htwo.le₂ htwo.quasi₁ htwo.quasi₂ htwo.odd₁
      htwo.odd₂ htwo.comm hAn₁' hAn₂' rfl rfl hD hF hDF (hm₁.trans hi)
  have hbot : (A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) = ⊥ ∨
      (A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) = ⊥ := by
    by_contra hcon
    rw [not_or] at hcon
    exact h.false_of_two_kernels_quasi hA htwo.le₁ htwo.le₂ htwo.quasi₁ htwo.quasi₂ htwo.odd₁
      htwo.odd₂ htwo.comm hAn₁' hAn₂' rfl rfl hcon.1 hcon.2 hDF (hm₁.trans hi)
  have hcard4 : Nat.card ↥A = 4 := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥A)).mp hel.isPGroup
    have hlog : mRank A = k := by
      rw [mRank, hk, Nat.log_pow (by norm_num : 1 < 2)]
    have hk2 : k ≤ 2 := by
      rcases hbot with hD | hF
      · have h1 := hm₁
        rw [hD, mOf_bot, hlog] at h1
        exact h1
      · have h2 := hm₂
        rw [hF, mOf_bot, hlog] at h2
        exact h2
    have hkge : 2 ≤ k := by
      rw [hk] at h4
      have h42 : 2 ^ 2 ≤ 2 ^ k := by
        rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
        exact h4
      exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp h42
    have hk2' : k = 2 := by omega
    rw [hk, hk2']
    norm_num
  refine ⟨hcard4, ?_⟩
  by_cases hD0 : (A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) = ⊥
  · rcases h.kernel_dichotomy_quasi htwo.quasi₂ htwo.odd₂ hA hr htwo.le₂ hAn₂' with hF0 | hcent₂
    · exact (br3_false_of_diagonal _rows.g3 h hVfix htwo hshape₁ hshape₂ hA hr hcard4 hAn₁
        hAn₂ hD0 hF0).elim
    · exact Or.inl ⟨hD0, hcent₂⟩
  · have hF0 : (A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) = ⊥ := by
      rcases hbot with h' | h'
      · exact absurd h' hD0
      · exact h'
    rcases h.kernel_dichotomy_quasi htwo.quasi₁ htwo.odd₁ hA hr htwo.le₁ hAn₁' with hDbot | hcent₁
    · exact absurd hDbot hD0
    · exact Or.inr ⟨hF0, hcent₁⟩

end CFSG.LocalAnalysis.WeakClosure81

end

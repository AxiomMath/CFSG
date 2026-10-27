module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Defs
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Diag
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Two

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem w183_i2_finite_lgl : Finite (LGL 2 V) :=
  Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
    (fun e f h => LinearEquiv.ext (congrFun h))

theorem br1_I2_member (hfin : FinG3) {Y L₁ L₂ T A : Subgroup (LGL 2 V)}
    {Γ : Set (Subgroup (LGL 2 V))} {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}
    (h : Assumption131 Y Γ VA i) (hVfix : ∀ B ∈ Γ, VA B ≤ fixSub B) (hi : 2 ≤ i)
    (htwo : Br2TwoComp Y T L₁ L₂)
    (hshape₁ : IsL2 ↥L₁ 2 ∨ IsL3 ↥L₁ 2 ∨ IsU3 ↥L₁ 2 ∨ IsSp4 ↥L₁ 2 ∨ IsL3 ↥L₁ 1 ∨
      IsAlt ↥L₁ 6)
    (hshape₂ : IsL2 ↥L₂ 2 ∨ IsL3 ↥L₂ 2 ∨ IsU3 ↥L₂ 2 ∨ IsSp4 ↥L₂ 2 ∨ IsL3 ↥L₂ 1 ∨
      IsAlt ↥L₂ 6)
    (hA : A ∈ Γ) (hr : mRank A ≤ i) (h4 : 4 ≤ Nat.card ↥A)
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
  haveI : Finite (LGL 2 V) := w183_i2_finite_lgl
  haveI := htwo.simple₁
  haveI := htwo.simple₂
  have hAn₁' : ∀ a ∈ A, ∀ l ∈ L₁, a * l * a⁻¹ ∈ L₁ := fun a ha l hl =>
    (Subgroup.mem_normalizer_iff.mp (hAn₁ ha) l).mp hl
  have hAn₂' : ∀ a ∈ A, ∀ l ∈ L₂, a * l * a⁻¹ ∈ L₂ := fun a ha l hl =>
    (Subgroup.mem_normalizer_iff.mp (hAn₂ ha) l).mp hl
  have hDF : (A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) ⊓
      (A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyD, hyF⟩ := hy
    obtain ⟨hyA, hyC₁⟩ := hyD
    obtain ⟨-, hyC₂⟩ := hyF
    refine htwo.cent y (h.le_G A hA hyA) ?_ ?_
    · intro l hl
      exact (Subgroup.mem_centralizer_iff.mp hyC₁ l hl).symm
    · intro l hl
      exact (Subgroup.mem_centralizer_iff.mp hyC₂ l hl).symm
  have hbot : (A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V))) = ⊥ ∨
      (A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) = ⊥ := by
    by_contra hcon
    rw [not_or] at hcon
    exact h.false_of_two_kernels
      (D := A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)))
      (F := A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
      hA htwo.le₁ htwo.le₂ htwo.nonab₁ htwo.nonab₂ htwo.comm hAn₁' hAn₂'
      rfl rfl hcon.1 hcon.2 hDF (hm₁.trans hi)
  have hcard4 : Nat.card ↥A = 4 := by
    have hAab : IsElemAbelian 2 A := h.isElemAb A hA
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥A)).mp hAab.isPGroup
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
  · rcases h.kernel_dichotomy hA hr htwo.nonab₂ htwo.le₂ hAn₂' with hF0 | hcent₂
    · exact (br1_false_of_diagonal hfin h hVfix htwo.nonab₁ htwo.nonab₂ htwo.le₁ htwo.le₂
        htwo.comm htwo.cent hshape₁ hshape₂ hA hr hcard4 (h.isElemAb A hA) hAn₁ hAn₂
        hD0 hF0).elim
    · exact Or.inl ⟨hD0, hcent₂⟩
  · have hF0 : (A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) = ⊥ := by
      rcases hbot with h | h
      · exact absurd h hD0
      · exact h
    rcases h.kernel_dichotomy hA hr htwo.nonab₁ htwo.le₁ hAn₁' with hDbot | hcent₁
    · exact absurd hDbot hD0
    · exact Or.inr ⟨hF0, hcent₁⟩

end CFSG.LocalAnalysis.WeakClosure81

end

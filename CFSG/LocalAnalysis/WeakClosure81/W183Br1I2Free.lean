module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1I2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem br1_I2_member_free (hfin : FinG3) {Y L₁ L₂ T A : Subgroup (LGL 2 V)}
    {Γ : Set (Subgroup (LGL 2 V))} {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}
    (h : Assumption131 Y Γ VA i) (hVfix : ∀ B ∈ Γ, VA B ≤ fixSub B) (hi : 2 ≤ i)
    (htwo : Br2TwoComp Y T L₁ L₂)
    (hshape₁ : IsL2 ↥L₁ 2 ∨ IsL3 ↥L₁ 2 ∨ IsU3 ↥L₁ 2 ∨ IsSp4 ↥L₁ 2 ∨ IsL3 ↥L₁ 1 ∨
      IsAlt ↥L₁ 6)
    (hshape₂ : IsL2 ↥L₂ 2 ∨ IsL3 ↥L₂ 2 ∨ IsU3 ↥L₂ 2 ∨ IsSp4 ↥L₂ 2 ∨ IsL3 ↥L₂ 1 ∨
      IsAlt ↥L₂ 6)
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
  have hr : mRank A ≤ i := by
    by_cases hD : A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥
    · rw [hD, mOf_bot] at hm₁
      omega
    by_cases hF : A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥
    · rw [hF, mOf_bot] at hm₂
      omega
    exfalso
    haveI := htwo.simple₁
    haveI := htwo.simple₂
    refine h.false_of_two_kernels hA htwo.le₁ htwo.le₂ htwo.nonab₁ htwo.nonab₂ htwo.comm
      (fun a ha l hl => (Subgroup.mem_normalizer_iff.mp (hAn₁ ha) l).mp hl)
      (fun a ha l hl => (Subgroup.mem_normalizer_iff.mp (hAn₂ ha) l).mp hl) rfl rfl hD hF ?_
      (hm₁.trans hi)
    rw [eq_bot_iff]
    rintro y ⟨⟨hyA, hy₁⟩, -, hy₂⟩
    exact Subgroup.mem_bot.mpr (htwo.cent y (h.le_G A hA hyA)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hy₁ l hl).symm)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hy₂ l hl).symm))
  exact br1_I2_member hfin h hVfix hi htwo hshape₁ hshape₂ hA hr h4 hAn₁ hAn₂ hm₁ hm₂

end CFSG.LocalAnalysis.WeakClosure81

end

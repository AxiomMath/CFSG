module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusTriDatum
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusLabel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis
  CFSG.ClassicalInvolution.G2D4Models.Twin

section Label

variable {F : Type} [Field F] [Finite F] [CharP F 2] {k : Type*} [Field k] [CharP k 2]
  {ρ : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F)}

theorem omPlus_dScalar_comp_triality (hρ : IsTrialityPinned ρ) (χ : spinGroup (quadPlus 4 F) → k)
    (hχ : ∀ a ∈ (omPlusCurtisDatum 4 F (by norm_num)).H,
      ∀ b ∈ (omPlusCurtisDatum 4 F (by norm_num)).H, χ (a * b) = χ a * χ b)
    (hχ1 : χ 1 = 1) (s : Fin 4) :
    (omPlusCurtisDatum 4 F (by norm_num)).dScalar (χ ∘ ρ) s =
      (omPlusCurtisDatum 4 F (by norm_num)).dScalar χ (triPerm s) := by
  have hn : 3 ≤ 4 := by norm_num
  have hH := (omPlusCurtisDatum_triality hρ).2.1
  have hχρ : ∀ a ∈ (omPlusCurtisDatum 4 F hn).H, ∀ b ∈ (omPlusCurtisDatum 4 F hn).H,
      (χ ∘ ρ) (a * b) = (χ ∘ ρ) a * (χ ∘ ρ) b := fun a ha b hb => by
    simpa only [Function.comp_apply, map_mul] using hχ (ρ a) (hH a ha) (ρ b) (hH b hb)
  have hχρ1 : (χ ∘ ρ) 1 = 1 := by simpa using hχ1
  by_cases h : ∀ a : Fˣ, χ (torusD F hn (triPerm s) a) = 1
  · rw [omq_omPlus_dScalar_eq_one hn χ (triPerm s) h,
      omq_omPlus_dScalar_eq_one hn (χ ∘ ρ) s fun a => by
        simpa only [Function.comp_apply, map_torusD_of_pinned hρ s a] using h a]
  · obtain ⟨a, ha⟩ := not_forall.mp h
    rw [omq_omPlus_dScalar_eq_zero hn χ hχ hχ1 (triPerm s) ⟨a, ha⟩,
      omq_omPlus_dScalar_eq_zero hn (χ ∘ ρ) hχρ hχρ1 s ⟨a, by
        simpa only [Function.comp_apply, map_torusD_of_pinned hρ s a] using ha⟩]

theorem omPlus_separating_comp_triality {V : Type*} [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadPlus 4 F)) V} {y : V}
    {χ : spinGroup (quadPlus 4 F) → k} {μ : Fin 4 → k}
    (ht : (omPlusCurtisDatum 4 F (by norm_num)).IsCurtisType σ y χ μ) (hρ : IsTrialityPinned ρ)
    (s : Fin 4) :
    (μ ∘ triPerm) s = (omPlusCurtisDatum 4 F (by norm_num)).dScalar (χ ∘ ρ) s ↔
      μ (triPerm s) = (omPlusCurtisDatum 4 F (by norm_num)).dScalar χ (triPerm s) := by
  rw [omPlus_dScalar_comp_triality hρ χ (fun a ha b hb => ht.chi_mul ha hb) ht.chi_one s]
  rfl

end Label

end CFSG.LocalAnalysis.WeakClosure81

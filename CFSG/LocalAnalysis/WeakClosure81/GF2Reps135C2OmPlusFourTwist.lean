module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtisComp
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusTriLabel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis
  CFSG.ClassicalInvolution.G2D4Models.Twin

theorem exists_twist_single_node {F : Type} [Field F] [Finite F] [CharP F 2] {k V : Type}
    [Field k] [CharP k 2] [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadPlus 4 F)) V} {y₀ : V}
    {χ : spinGroup (quadPlus 4 F) → k} {μ : Fin 4 → k}
    (ht : (omPlusCurtisDatum 4 F (by norm_num)).IsCurtisType σ y₀ χ μ)
    {ρ₀ : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F)} (hρ₀ : IsTrialityPinned ρ₀)
    {j : Fin 4}
    (hJ : ∀ i : Fin 4, μ i = (omPlusCurtisDatum 4 F (by norm_num)).dScalar χ i ↔ i = triPerm j) :
    (omPlusCurtisDatum 4 F (by norm_num)).IsCurtisType (σ.comp ρ₀.toMonoidHom) y₀ (χ ∘ ρ₀)
      (μ ∘ triPerm) ∧
    ∀ i : Fin 4, (μ ∘ triPerm) i = (omPlusCurtisDatum 4 F (by norm_num)).dScalar (χ ∘ ρ₀) i ↔
      i = j := by
  obtain ⟨hU, hH, hX, hn⟩ := omPlusCurtisDatum_triality hρ₀
  refine ⟨isCurtisType_comp ht ρ₀ triPerm hU hH hX hn, fun i => ?_⟩
  exact (omPlus_separating_comp_triality ht hρ₀ i).trans
    ((hJ (triPerm i)).trans
      ⟨fun h => triEquiv.injective h, fun h => by rw [h]⟩)

theorem exists_twist_node_zero {F : Type} [Field F] [Finite F] [CharP F 2] {k V : Type}
    [Field k] [CharP k 2] [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadPlus 4 F)) V} {y₀ : V}
    {χ : spinGroup (quadPlus 4 F) → k} {μ : Fin 4 → k}
    (ht : (omPlusCurtisDatum 4 F (by norm_num)).IsCurtisType σ y₀ χ μ) {i₀ : Fin 4}
    (hi₀ : i₀.val ≠ 1)
    (hJ : ∀ i : Fin 4, μ i = (omPlusCurtisDatum 4 F (by norm_num)).dScalar χ i ↔ i = i₀) :
    ∃ (γ : spinGroup (quadPlus 4 F) ≃* spinGroup (quadPlus 4 F))
      (χ' : spinGroup (quadPlus 4 F) → k) (μ' : Fin 4 → k),
      (omPlusCurtisDatum 4 F (by norm_num)).IsCurtisType (σ.comp γ.toMonoidHom) y₀ χ' μ' ∧
      ∀ i : Fin 4, μ' i = (omPlusCurtisDatum 4 F (by norm_num)).dScalar χ' i ↔ i.val = 0 := by
  obtain ⟨ρ₀, hρ₀⟩ := exists_trialityPinned (F := F)
  fin_cases i₀
  · have hrefl : (MulEquiv.refl (spinGroup (quadPlus 4 F))).toMonoidHom =
        MonoidHom.id (spinGroup (quadPlus 4 F)) := MulEquiv.toMonoidHom_refl
    refine ⟨MulEquiv.refl _, χ, μ, ?_, fun i => (hJ i).trans Fin.val_eq_zero_iff.symm⟩
    rw [hrefl, MonoidHom.comp_id]
    exact ht
  · exact absurd rfl hi₀
  · obtain ⟨ht1, hJ1⟩ := exists_twist_single_node ht hρ₀ (j := 0) hJ
    exact ⟨ρ₀, χ ∘ ρ₀, μ ∘ triPerm, ht1,
      fun i => (hJ1 i).trans Fin.val_eq_zero_iff.symm⟩
  · obtain ⟨ht1, hJ1⟩ := exists_twist_single_node ht hρ₀ (j := 2) hJ
    obtain ⟨ht2, hJ2⟩ := exists_twist_single_node ht1 hρ₀ (j := 0) hJ1
    refine ⟨ρ₀.trans ρ₀, (χ ∘ ρ₀) ∘ ρ₀, (μ ∘ triPerm) ∘ triPerm, ?_,
      fun i => (hJ2 i).trans Fin.val_eq_zero_iff.symm⟩
    have htrans : (ρ₀.trans ρ₀).toMonoidHom = ρ₀.toMonoidHom.comp ρ₀.toMonoidHom :=
      MulEquiv.toMonoidHom_trans ρ₀ ρ₀
    rw [htrans, ← MonoidHom.comp_assoc]
    exact ht2

end CFSG.LocalAnalysis.WeakClosure81

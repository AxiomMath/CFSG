module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoDef
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

private lemma s16k_permAct_inv_apply (n : ℕ) (σ : Equiv.Perm (Fin n)) (m : G6.PermMod n) :
    G6.permAct n σ⁻¹ (G6.permAct n σ m) = m := by
  rw [← permAct_mul_act n σ⁻¹ σ m, inv_mul_cancel, permAct_one_act]

private lemma s16k_altDn_mem_core_iff (n : ℕ) (σ : Equiv.Perm (Fin n)) (m : G6.PermMod n) :
    G6.permAct n σ m ∈ G6.coreMod n ↔ m ∈ G6.coreMod n := by
  refine ⟨fun hm => ?_, fun hm => G6.permAct_mem_coreMod σ hm⟩
  have h := G6.permAct_mem_coreMod σ⁻¹ hm
  rwa [s16k_permAct_inv_apply n σ m] at h

private lemma s16k_altDn_mem_zpowers_iff (n : ℕ) (σ : Equiv.Perm (Fin n)) (m : G6.PermMod n) :
    G6.permAct n σ m ∈ Subgroup.zpowers (G6.allOnes n) ↔
      m ∈ Subgroup.zpowers (G6.allOnes n) := by
  refine ⟨fun hm => ?_, fun hm => permAct_mem_zpowers_allOnes n σ hm⟩
  have h := permAct_mem_zpowers_allOnes n σ⁻¹ hm
  rwa [s16k_permAct_inv_apply n σ m] at h

private lemma s16k_altDn_mem_ker_iff (n : ℕ) (σ : Equiv.Perm (Fin n)) (m : G6.PermMod n) :
    G6.permAct n σ m ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n ↔
      m ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨(s16k_altDn_mem_zpowers_iff n σ m).1 h.1,
      (s16k_altDn_mem_core_iff n σ m).1 h.2⟩,
    fun h => ⟨(s16k_altDn_mem_zpowers_iff n σ m).2 h.1,
      (s16k_altDn_mem_core_iff n σ m).2 h.2⟩⟩

private lemma s16k_permAct_conj (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (m : G6.PermMod n) :
    G6.permAct n σ (G6.permAct n τ m) =
      G6.permAct n (σ * τ * σ⁻¹) (G6.permAct n σ m) := by
  rw [permAct_mul_act n (σ * τ) σ⁻¹ (G6.permAct n σ m)]
  rw [s16k_permAct_inv_apply n σ m]
  rw [permAct_mul_act n σ τ m]

theorem s16k_alt_two_equiv {n : ℕ} (hn : 7 ≤ n) {X : Type} [Group X] [Finite X]
    (hX : UC22.IsAlt X n) {π₁ π₂ : (FFModel.altDn n).Gam →* X} (hπ₁ : Function.Surjective π₁)
    (hπ₂ : Function.Surjective π₂) :
    Function.Injective π₁ ∧ Function.Injective π₂ ∧
      S16kModelsEquivVia (FFModel.altDn n) (FFModel.altDn n).act (FFModel.altDn n) π₁ π₂ := by
  obtain ⟨e⟩ := hX
  have hinj₁ : Function.Injective π₁ :=
    (Finite.injective_iff_surjective_of_equiv
      (e.symm : ↥(alternatingGroup (Fin n)) ≃ X)).2 hπ₁
  have hinj₂ : Function.Injective π₂ :=
    (Finite.injective_iff_surjective_of_equiv
      (e.symm : ↥(alternatingGroup (Fin n)) ≃ X)).2 hπ₂
  refine ⟨hinj₁, hinj₂, ?_⟩
  let π₂e : (FFModel.altDn n).Gam ≃* X := MulEquiv.ofBijective π₂ ⟨hinj₂, hπ₂⟩
  let φ : MulAut (FFModel.altDn n).Gam :=
    MulEquiv.ofBijective ((π₂e.symm : X ≃* (FFModel.altDn n).Gam).toMonoidHom.comp π₁) (by
      refine ⟨fun a b hab => ?_, fun y => ?_⟩
      · apply hinj₁
        exact π₂e.symm.injective hab
      · obtain ⟨a, ha⟩ := hπ₁ (π₂e y)
        refine ⟨a, ?_⟩
        show π₂e.symm (π₁ a) = y
        rw [ha, MulEquiv.symm_apply_apply])
  obtain ⟨σ, hσ⟩ :=
    CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le (Or.inr hn) φ
  refine ⟨G6.permAct n σ, ?_, ?_, ?_⟩
  · intro m
    exact (s16k_altDn_mem_core_iff n σ m).symm
  · intro m
    exact (s16k_altDn_mem_ker_iff n σ m).symm
  · intro γ₁ γ₂ hπ m
    have hγ₂ : γ₂ = φ γ₁ := by
      show γ₂ = π₂e.symm (π₁ γ₁)
      have h : π₂e.symm (π₁ γ₁) = γ₂ := by
        rw [MulEquiv.symm_apply_eq]
        exact hπ
      exact h.symm
    have hcoe : γ₂.val = σ * γ₁.val * σ⁻¹ := by
      rw [hγ₂]
      exact hσ γ₁
    show G6.permAct n σ (G6.permAct n γ₁.val m) =
      G6.permAct n γ₂.val (G6.permAct n σ m)
    rw [hcoe]
    exact s16k_permAct_conj n σ γ₁.val m

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

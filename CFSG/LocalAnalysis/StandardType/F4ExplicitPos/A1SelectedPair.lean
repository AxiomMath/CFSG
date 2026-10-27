module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NativePinFinalPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedPair
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalA1Part1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.A1SelectedPair

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.StandardType.F4ExplicitPos.RationalA1

open CFSG.StandardType.F4ExplicitPos.RationalA2Finish

open CFSG.StandardType.F4ExplicitPos.NativePinFinal

open CFSG.StandardType.F4ExplicitPos.SelectedPair

open scoped Matrix

theorem conjugatedRootRange_one_le_range_phiA1_pos
    {Ω : Type} [Field Ω] [CharP Ω 2]
    {k : Type} [Field k] [Algebra k Ω] (z : ModGL Tag.F4 Ω) {γ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot Tag.F4 γ) :
    conjugatedRootRange (k := k) z γ 1 ≤ (phiA1 (k := k) z γ).range := by
  intro x hx
  rw [mem_conjugatedRootRange_iff (k := k) z γ 1 x] at hx
  obtain ⟨t, rfl⟩ := hx
  refine MonoidHom.mem_range.mpr ⟨uSL t, ?_⟩
  rw [phiA1, MonoidHom.comp_apply, MonoidHom.comp_apply]
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [map_uSL_a1,
    CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two
      (CharP.cast_eq_zero Ω 2) γ (algebraMap k Ω t)]
  simp

theorem conjugatedRootRange_one_le_range_phiA1_neg
    {Ω : Type} [Field Ω] [CharP Ω 2]
    {k : Type} [Field k] [Algebra k Ω] (z : ModGL Tag.F4 Ω) {γ : Fin Tag.F4.rank → ℤ}
    (hγ : IsRoot Tag.F4 γ) :
    conjugatedRootRange (k := k) z (-γ) 1 ≤ (phiA1 (k := k) z γ).range := by
  intro x hx
  rw [mem_conjugatedRootRange_iff (k := k) z (-γ) 1 x] at hx
  obtain ⟨t, rfl⟩ := hx
  refine MonoidHom.mem_range.mpr ⟨vSL t, ?_⟩
  rw [phiA1, MonoidHom.comp_apply, MonoidHom.comp_apply]
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [map_vSL_a1,
    CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_vSL_of_two
      (CharP.cast_eq_zero Ω 2) hγ (algebraMap k Ω t)]
  simp

theorem f4_a1_selected_pair_output
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {k : Type} [Field k] [Finite k] [Algebra k Ω]
    (D : LangDatum Tag.F4 Ω) (f : ℕ) (hf : 1 ≤ f) (hq : D.q = 2 ^ f)
    (hk : Nat.card k = 2 ^ f)
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hρ : FrobRootMap D ρ)
    (i : KernelComponent χ)
    (hker : ∀ α ∈ kernelRoots χ, ρ α ∈ kernelRoots χ)
    (hstable : (fun α => ρ α) '' componentRoots χ i = componentRoots χ i)
    {γ : Fin Tag.F4.rank → ℤ} (hΨ : componentRoots χ i = {γ, -γ})
    {Ccent : Subgroup (ModGL Tag.F4 Ω)} {P : Subgroup (ModGL Tag.F4 Ω)}
    (hP : CFSG.Assembly.IsComponentOf P (D.Γ ⊓ Ccent))
    (hPleH : P ≤ rootSpan Tag.F4 Ω (componentRoots χ i))
    (hHcent : rootSpan Tag.F4 Ω (componentRoots χ i) ≤ Ccent) :
    SelectedPairOutput (k := k) D χ P i := by
  have hγmem : γ ∈ componentRoots χ i := by rw [hΨ]; simp
  have hγr : IsRoot Tag.F4 γ := isRoot_of_mem_componentRoots hγmem
  have hinner : twistInner (componentRoots χ i) ρ := by
    have hργ : ρ γ ∈ componentRoots χ i := by
      rw [← hstable]; exact ⟨γ, hγmem, rfl⟩
    have hργ' : ρ γ = γ ∨ ρ γ = -γ := by
      have h := hργ
      rw [hΨ] at h
      simpa using h
    have hδ' : ∀ {δ : Fin Tag.F4.rank → ℤ}, δ ∈ componentRoots χ i →
        δ = γ ∨ δ = -γ := by
      intro δ hδ
      have h := hδ
      rw [hΨ] at h
      simpa using h
    rcases hργ' with hργ_eq | hργ_neg
    · refine ⟨1, Subgroup.one_mem _, ?_⟩
      intro δ hδ
      rcases hδ' hδ with rfl | rfl
      · simpa using hργ_eq
      · simp [hρ.neg_eq, hργ_eq]
    · refine ⟨rootReflection γ, Subgroup.subset_closure ⟨γ, hγmem, rfl⟩, ?_⟩
      intro δ hδ
      rcases hδ' hδ with rfl | rfl
      · simp [hργ_neg, CFSG.LieType.Chevalley.rootReflection_smul_self hγr]
      · simp [hρ.neg_eq, hργ_neg, smul_neg, CFSG.LieType.Chevalley.rootReflection_smul_self hγr]
  obtain ⟨σ, z, hσc, hzZ, hnorm, hgoal⟩ :=
    CFSG.StandardType.F4ExplicitPos.NativePinFinal.exists_untwist_one_step_native
      D f hf hq ρ hρ i hker hinner
  have hσ : ∀ c, σ c = c ^ Nat.card k := fun c => by rw [hσc c, hq, hk]
  have hcomp : (rootSL2 Tag.F4 Ω γ).range =
      rootSpan Tag.F4 Ω (componentRoots χ i) := by
    rw [hΨ, CFSG.LieType.HighestRoot.rootSpan_pair_eq γ, rootSL2_range_eq_sup hγr]
  have hzH : ∀ g, g ∈ (rootSL2 Tag.F4 Ω γ).range ↔
      z * g * z⁻¹ ∈ (rootSL2 Tag.F4 Ω γ).range := by
    intro g
    rw [hcomp]
    exact normalizesAll_apply hnorm i g
  have hzF : ∀ g ∈ (rootSL2 Tag.F4 Ω γ).range,
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
    intro g hg
    rw [hcomp] at hg
    exact hgoal g hg
  have hNdef : (phiA1 (k := k) z γ).range =
      rootSpan Tag.F4 Ω (componentRoots χ i) ⊓ D.model := by
    rw [phiA1_range_of_normalizes (k := k) D σ hσ z γ hγr hzH hzF, hcomp]
  have hPleΓ : P ≤ D.Γ := hP.1.trans inf_le_left
  have hPleM : P ≤ D.model := hPleΓ.trans (Subgroup.commutator_le_self D.model)
  have hPleN : P ≤ (phiA1 (k := k) z γ).range := by
    rw [hNdef]; exact le_inf hPleH hPleM
  by_cases hf1 : f = 1
  ·
    have hk2 : Nat.card k = 2 := by rw [hk, hf1]; norm_num
    have hNsolv : Group.IsSolvable ↥(phiA1 (k := k) z γ).range := by
      have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) k) :=
        CFSG.StandardType.F4ExplicitPos.RationalA1.isSolvable_SL2_card_two hk2
      let e := MonoidHom.ofInjective
        (CFSG.StandardType.F4ExplicitPos.RationalA1.phiA1_injective (Ω := Ω) (k := k) z γ)
      exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    have : Group.IsSolvable ↥(phiA1 (k := k) z γ).range := hNsolv
    have hPq' : CFSG.IsQuasisimple ↥P :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥P).mp hP.2.2
    have : Group.IsPerfect ↥P := hPq'.1
    have : Nontrivial ↥P := CFSG.LocalCores.isQuasisimple_nontrivial hPq'
    have hPsolv : Group.IsSolvable ↥P :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hPleN)
        (Subgroup.inclusion_injective hPleN)
    exact (Group.IsPerfect.not_isSolvable ↥P hPsolv).elim
  ·
    have hf2 : 2 ≤ f := by
      by_contra h
      have h_eq : f = 1 := by omega
      exact hf1 h_eq
    have h4 : 4 ≤ Nat.card k := by
      rw [hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    have hNq : CFSG.IsQuasisimple ↥(phiA1 (k := k) z γ).range :=
      CFSG.StandardType.F4ExplicitPos.RationalA1.isQuasisimple_range_phiA1 z γ h4
    have hNleM : (phiA1 (k := k) z γ).range ≤ D.model := by
      rw [hNdef]; exact inf_le_right
    have hNleH : (phiA1 (k := k) z γ).range ≤ rootSpan Tag.F4 Ω (componentRoots χ i) := by
      rw [hNdef]; exact inf_le_left
    have hNΓ : (phiA1 (k := k) z γ).range ≤ D.Γ := by
      have : Group.IsPerfect ↥(phiA1 (k := k) z γ).range := hNq.1
      calc (phiA1 (k := k) z γ).range
          = ⁅(phiA1 (k := k) z γ).range, (phiA1 (k := k) z γ).range⁆ :=
            Subgroup.commutator_eq_self.symm
        _ ≤ ⁅D.model, D.model⁆ := Subgroup.commutator_mono hNleM hNleM
        _ = D.Γ := rfl
    have hNleC : (phiA1 (k := k) z γ).range ≤ D.Γ ⊓ Ccent :=
      le_inf hNΓ (hNleH.trans hHcent)
    have hPN : P = (phiA1 (k := k) z γ).range :=
      RationalC3Attach.eq_of_isComponentOf_of_fixed_quasisimple_of_le_actual
        (C := D.Γ ⊓ Ccent) (M := D.model) (Γ := D.Γ)
        (H := rootSpan Tag.F4 Ω (componentRoots χ i))
        (N := (phiA1 (k := k) z γ).range) (K := P)
        hNdef (Subgroup.commutator_le_self D.model) hNleC hNq hP hPleH hPleΓ hP.2.2
    have hPle : conjugatedRootRange (k := k) z γ 1 ≤ P := by
      rw [hPN]
      exact conjugatedRootRange_one_le_range_phiA1_pos (k := k) z hγr
    have hPlem : conjugatedRootRange (k := k) z (-γ) 1 ≤ P := by
      rw [hPN]
      exact conjugatedRootRange_one_le_range_phiA1_neg (k := k) z hγr
    exact CFSG.StandardType.F4ExplicitPos.SelectedPair.selected_pair_output_of
      (k := k) D hγmem hzZ 1 1 hPle hPlem hgoal

end CFSG.StandardType.F4ExplicitPos.A1SelectedPair

end

end

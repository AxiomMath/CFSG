module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CommonPairTransport
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NativePinFinalPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.RationalA2FinishPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.SelectedPair

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.StandardType.F4ExplicitPos.RationalA2Finish

open CFSG.StandardType.F4ExplicitPos.NativePinFinal

open CFSG.StandardType.F4ExplicitPos.CommonPairTransport

open scoped Matrix

def SelectedPairOutput
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (D : LangDatum Tag.F4 Ω) {k : Type} [Field k] [Algebra k Ω]
    {M : Type*} [CommGroup M] (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M)
    (Jbar : Subgroup (ModGL Tag.F4 Ω)) (i : KernelComponent χ) : Prop :=
  ∃ α ∈ componentRoots χ i, ∃ wD ∈ Zsub χ, ∃ ε εm : Ωˣ,
    conjugatedRootRange (k := k) wD α ε ≤ Jbar ∧
    conjugatedRootRange (k := k) wD (-α) εm ≤ Jbar ∧
    Nat.card (conjugatedRootRange (k := k) wD α ε) = Nat.card k ∧
    Nat.card (conjugatedRootRange (k := k) wD (-α) εm) = Nat.card k ∧
    ((rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom).map D.step =
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom ∧
    ((rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj wD).toMonoidHom).map D.step =
      (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj wD).toMonoidHom

theorem rootSubgroup_map_frobGL
    {τ : Tag} {Ω : Type} [Field Ω] (σ : Ω ≃+* Ω)
    (α : Fin τ.rank → ℤ) :
    (rootSubgroup τ Ω α).map (frobGL σ) = rootSubgroup τ Ω α := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_rootSubgroup] at hy ⊢
    obtain ⟨c, rfl⟩ := hy
    exact ⟨σ c, (frobGL_pinnedX_native σ α c).symm⟩
  · intro x hx
    rw [mem_rootSubgroup] at hx
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := σ.surjective c
    rw [Subgroup.mem_map]
    exact ⟨pinnedX τ Ω α d, by rw [mem_rootSubgroup]; exact ⟨d, rfl⟩,
      frobGL_pinnedX_native σ α d⟩

theorem rootSubgroup_conj_step_stable
    {τ : Tag} {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (D : LangDatum τ Ω) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}
    {σ : Ω ≃+* Ω} {wD : ModGL τ Ω}
    (hstep : ∀ g ∈ rootSpan τ Ω (componentRoots χ i),
      D.step (wD * g * wD⁻¹) = wD * frobGL σ g * wD⁻¹)
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) :
    ((rootSubgroup τ Ω α).map (MulAut.conj wD).toMonoidHom).map D.step =
      (rootSubgroup τ Ω α).map (MulAut.conj wD).toMonoidHom := by
  have hspan : rootSubgroup τ Ω α ≤ rootSpan τ Ω (componentRoots χ i) := by
    obtain ⟨hk, hi⟩ := hα
    exact hi ▸ CFSG.LieType.Chevalley.rootSubgroup_le_componentRootSpan (χ := χ) (K := Ω)
      (⟨α, hk⟩ : kernelRoots χ)
  have hpoint : ∀ x ∈ rootSubgroup τ Ω α,
      D.step ((MulAut.conj wD).toMonoidHom x) =
        (MulAut.conj wD).toMonoidHom (frobGL σ x) := by
    intro x hx
    change D.step (wD * x * wD⁻¹) = wD * (frobGL σ) x * wD⁻¹
    exact hstep x (hspan hx)
  have hmap : (rootSubgroup τ Ω α).map
        (D.step.comp (MulAut.conj wD).toMonoidHom) =
      (rootSubgroup τ Ω α).map
        ((MulAut.conj wD).toMonoidHom.comp (frobGL σ)) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_map] at hx ⊢
      obtain ⟨y, hy, hxy⟩ := hx
      have hx' : D.step ((MulAut.conj wD).toMonoidHom y) = x := by
        simpa only [MonoidHom.comp_apply] using hxy
      exact ⟨y, hy, (hpoint y hy).symm.trans hx'⟩
    · intro x hx
      rw [Subgroup.mem_map] at hx ⊢
      obtain ⟨y, hy, hxy⟩ := hx
      have hx' : (MulAut.conj wD).toMonoidHom ((frobGL σ) y) = x := by
        simpa only [MonoidHom.comp_apply] using hxy
      exact ⟨y, hy, (hpoint y hy).trans hx'⟩
  calc ((rootSubgroup τ Ω α).map (MulAut.conj wD).toMonoidHom).map D.step
      = (rootSubgroup τ Ω α).map (D.step.comp (MulAut.conj wD).toMonoidHom) :=
        Subgroup.map_map _ _ _
    _ = (rootSubgroup τ Ω α).map ((MulAut.conj wD).toMonoidHom.comp (frobGL σ)) := hmap
    _ = ((rootSubgroup τ Ω α).map (frobGL σ)).map (MulAut.conj wD).toMonoidHom :=
        (Subgroup.map_map _ _ _).symm
    _ = (rootSubgroup τ Ω α).map (MulAut.conj wD).toMonoidHom := by
        rw [rootSubgroup_map_frobGL]

theorem selected_pair_output_of
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (D : LangDatum Tag.F4 Ω) {k : Type} [Field k] [Algebra k Ω]
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M} {i : KernelComponent χ}
    {Jbar : Subgroup (ModGL Tag.F4 Ω)}
    {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ componentRoots χ i)
    {wD : ModGL Tag.F4 Ω} (hwD : wD ∈ Zsub χ) (ε εm : Ωˣ)
    (hP : conjugatedRootRange (k := k) wD α ε ≤ Jbar)
    (hPm : conjugatedRootRange (k := k) wD (-α) εm ≤ Jbar)
    {σ : Ω ≃+* Ω}
    (hstep : ∀ g ∈ rootSpan Tag.F4 Ω (componentRoots χ i),
      D.step (wD * g * wD⁻¹) = wD * frobGL σ g * wD⁻¹) :
    SelectedPairOutput (k := k) D χ Jbar i := by
  refine ⟨α, hα, wD, hwD, ε, εm, hP, hPm, ?_, ?_, ?_, ?_⟩
  · exact conjugatedRootRange_card wD α ε
  · exact conjugatedRootRange_card wD (-α) εm
  · exact rootSubgroup_conj_step_stable D hstep hα
  · exact rootSubgroup_conj_step_stable D hstep ((isRootComponent_componentRoots i).neg_mem α hα)

theorem selectedPairOutput_of_curves
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (D : LangDatum Tag.F4 Ω) {k : Type} [Field k] [Algebra k Ω]
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M} {i : KernelComponent χ}
    {Jbar : Subgroup (ModGL Tag.F4 Ω)}
    {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ componentRoots χ i)
    {wD : ModGL Tag.F4 Ω} (hwD : wD ∈ Zsub χ) (ε εm : Ωˣ)
    (hP : conjugatedRootRange (k := k) wD α ε ≤ Jbar)
    (hPm : conjugatedRootRange (k := k) wD (-α) εm ≤ Jbar)
    (hcard : Nat.card (conjugatedRootRange (k := k) wD α ε) = Nat.card k)
    (hcardm : Nat.card (conjugatedRootRange (k := k) wD (-α) εm) = Nat.card k)
    (hstab : ((rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom).map D.step =
      (rootSubgroup Tag.F4 Ω α).map (MulAut.conj wD).toMonoidHom)
    (hstabm : ((rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj wD).toMonoidHom).map D.step =
      (rootSubgroup Tag.F4 Ω (-α)).map (MulAut.conj wD).toMonoidHom) :
    SelectedPairOutput (k := k) D χ Jbar i :=
  ⟨α, hα, wD, hwD, ε, εm, hP, hPm, hcard, hcardm, hstab, hstabm⟩

end CFSG.StandardType.F4ExplicitPos.SelectedPair

end

end

module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.NativePinFinalPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.SelectedPair

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.InnerSelectedPair

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.StandardType.F4ExplicitPos.SelectedPair

open CFSG.StandardType.F4ExplicitPos.RationalA2Finish

open CFSG.StandardType.F4ExplicitPos.NativePinFinal

open CFSG.StandardType.F4ExplicitPos.CommonPairTransport

open scoped Matrix

theorem frobenius_algebraMap_fixed {Ω k : Type} [Field Ω] [Field k] [Finite k] [Algebra k Ω]
    (σ : Ω ≃+* Ω) (hσ : ∀ c, σ c = c ^ Nat.card k) (t : k) :
    σ (algebraMap k Ω t) = algebraMap k Ω t :=
  DFunLike.congr_fun (CFSG.LieType.Chevalley.frobenius_comp_algebraMap σ.toRingHom hσ) t

theorem frobGL_pinnedX_algebraMap_fixed
    {Ω k : Type} [Field Ω] [Field k] [Finite k] [Algebra k Ω]
    (σ : Ω ≃+* Ω) (hσ : ∀ c, σ c = c ^ Nat.card k) (α : Fin Tag.F4.rank → ℤ) (t : k) :
    frobGL σ (pinnedX Tag.F4 Ω α (algebraMap k Ω t)) =
      pinnedX Tag.F4 Ω α (algebraMap k Ω t) := by
  rw [frobGL_pinnedX_native, frobenius_algebraMap_fixed σ hσ t]

theorem inner_conj_pinnedX_mem_model
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (D : LangDatum Tag.F4 Ω) {k : Type} [Field k] [Algebra k Ω] [Finite k]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {i : KernelComponent χ} {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ componentRoots χ i)
    {z : ModGL Tag.F4 Ω} (hz : z ∈ Zsub χ)
    {σ : Ω ≃+* Ω} (hσ : ∀ c, σ c = c ^ Nat.card k)
    (hstep : ∀ g ∈ rootSpan Tag.F4 Ω (componentRoots χ i),
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (t : k) :
    z * pinnedX Tag.F4 Ω α (algebraMap k Ω t) * z⁻¹ ∈ D.model := by
  have hXroot : pinnedX Tag.F4 Ω α (algebraMap k Ω t) ∈ rootSubgroup Tag.F4 Ω α :=
    Subgroup.subset_closure ⟨algebraMap k Ω t, rfl⟩
  have hspan : rootSubgroup Tag.F4 Ω α ≤ rootSpan Tag.F4 Ω (componentRoots χ i) :=
    rootSubgroup_le_componentRootSpan_of_mem_componentRoots (Ω := Ω) hα
  have hzadj : z ∈ adjointGroup Tag.F4 Ω := Zsub_le_adjointGroup χ hz
  have hfixed : D.step (z * pinnedX Tag.F4 Ω α (algebraMap k Ω t) * z⁻¹) =
      z * pinnedX Tag.F4 Ω α (algebraMap k Ω t) * z⁻¹ := by
    rw [hstep _ (hspan hXroot), frobGL_pinnedX_algebraMap_fixed σ hσ α t]
  rw [LangDatum.mem_model]
  refine ⟨?_, ?_⟩
  · exact mul_mem (mul_mem hzadj (rootSubgroup_le_adjointGroup α hXroot)) (inv_mem hzadj)
  · simpa [LangDatum.step, MulAut.conj_apply] using hfixed

theorem inner_conj_pinnedX_mem_Jbar
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (D : LangDatum Tag.F4 Ω) {k : Type} [Field k] [Algebra k Ω] [Finite k]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {i : KernelComponent χ} {Jbar H : Subgroup (ModGL Tag.F4 Ω)}
    {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ componentRoots χ i)
    {z : ModGL Tag.F4 Ω} (hz : z ∈ Zsub χ)
    (hH : H = rootSpan Tag.F4 Ω (componentRoots χ i))
    (hnorm : ∀ g : ModGL Tag.F4 Ω, g ∈ H ↔ z * g * z⁻¹ ∈ H)
    {σ : Ω ≃+* Ω} (hσ : ∀ c, σ c = c ^ Nat.card k)
    (hstep : ∀ g ∈ H, D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hJ : Jbar = H ⊓ D.model) (t : k) :
    z * pinnedX Tag.F4 Ω α (algebraMap k Ω t) * z⁻¹ ∈ Jbar := by
  have hstep' : ∀ g ∈ rootSpan Tag.F4 Ω (componentRoots χ i),
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
    intro g hg
    exact hstep g (by rw [hH]; exact hg)
  have hmodel := inner_conj_pinnedX_mem_model D hα hz hσ hstep' t
  have hXH : pinnedX Tag.F4 Ω α (algebraMap k Ω t) ∈ H := by
    rw [hH]
    exact rootSubgroup_le_componentRootSpan_of_mem_componentRoots (Ω := Ω) hα
      (Subgroup.subset_closure ⟨algebraMap k Ω t, rfl⟩)
  have hHmem : z * pinnedX Tag.F4 Ω α (algebraMap k Ω t) * z⁻¹ ∈ H :=
    (hnorm _).mp hXH
  rw [hJ]
  exact ⟨hHmem, hmodel⟩

theorem inner_selected_pair_output
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (D : LangDatum Tag.F4 Ω) {k : Type} [Field k] [Algebra k Ω] [Finite k]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {i : KernelComponent χ} {Jbar H : Subgroup (ModGL Tag.F4 Ω)}
    {α : Fin Tag.F4.rank → ℤ} (hα : α ∈ componentRoots χ i)
    {z : ModGL Tag.F4 Ω} (hz : z ∈ Zsub χ)
    (hH : H = rootSpan Tag.F4 Ω (componentRoots χ i))
    (hnorm : ∀ g : ModGL Tag.F4 Ω, g ∈ H ↔ z * g * z⁻¹ ∈ H)
    {σ : Ω ≃+* Ω} (hσ : ∀ c, σ c = c ^ Nat.card k)
    (hstep : ∀ g ∈ H, D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hJ : Jbar = H ⊓ D.model) :
    SelectedPairOutput (k := k) D χ Jbar i := by
  have hstep' : ∀ g ∈ rootSpan Tag.F4 Ω (componentRoots χ i),
      D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
    intro g hg
    exact hstep g (by rw [hH]; exact hg)
  have hneg : -α ∈ componentRoots χ i := (isRootComponent_componentRoots i).neg_mem α hα
  refine selected_pair_output_of (k := k) D hα hz 1 1 ?_ ?_ hstep'
  · intro y hy
    obtain ⟨t, rfl⟩ := (mem_conjugatedRootRange_iff (k := k) z α 1 y).mp hy
    simp only [Units.val_one, one_mul]
    exact inner_conj_pinnedX_mem_Jbar D hα hz hH hnorm hσ hstep hJ t
  · intro y hy
    obtain ⟨t, rfl⟩ := (mem_conjugatedRootRange_iff (k := k) z (-α) 1 y).mp hy
    simp only [Units.val_one, one_mul]
    exact inner_conj_pinnedX_mem_Jbar D hneg hz hH hnorm hσ hstep hJ t

theorem inner_selected_pair_output_exists
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    (D : LangDatum Tag.F4 Ω) {k : Type} [Field k] [Algebra k Ω] [Finite k]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {i : KernelComponent χ} {Jbar H : Subgroup (ModGL Tag.F4 Ω)}
    {z : ModGL Tag.F4 Ω} (hz : z ∈ Zsub χ)
    (hH : H = rootSpan Tag.F4 Ω (componentRoots χ i))
    (hnorm : ∀ g : ModGL Tag.F4 Ω, g ∈ H ↔ z * g * z⁻¹ ∈ H)
    {σ : Ω ≃+* Ω} (hσ : ∀ c, σ c = c ^ Nat.card k)
    (hstep : ∀ g ∈ H, D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hJ : Jbar = H ⊓ D.model) :
    SelectedPairOutput (k := k) D χ Jbar i := by
  classical
  let α : Fin Tag.F4.rank → ℤ := (Quotient.out i).1
  have hα : α ∈ componentRoots χ i := by
    refine ⟨(Quotient.out i).2, ?_⟩
    have h : (⟨α, (Quotient.out i).2⟩ : kernelRoots χ) = Quotient.out i := Subtype.ext rfl
    rw [h]
    change (Quotient.mk (kernelRootSetoid χ) (Quotient.out i) : KernelComponent χ) = i
    exact Quotient.out_eq i
  exact inner_selected_pair_output D hα hz hH hnorm hσ hstep hJ

end CFSG.StandardType.F4ExplicitPos.InnerSelectedPair

end

end

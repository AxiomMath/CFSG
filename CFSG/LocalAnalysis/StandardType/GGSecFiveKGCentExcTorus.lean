module

public import CFSG.LieType.Chevalley.BorelSelfNormalizer
import CFSG.LieType.Chevalley.IntrinsicSimplePairs
import CFSG.LieType.Chevalley.OppositeBorel

public section

namespace CFSG.StandardType.KGCentExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem mem_torusGroup_of_forall_mem_normalizer_rootSubgroup
    {τ : Tag} {K : Type} [Field K] {h : ModGL τ K} (hh : h ∈ adjointGroup τ K)
    (hN : ∀ γ, IsRoot τ γ → h ∈ Subgroup.normalizer (rootSubgroup τ K γ : Set (ModGL τ K))) :
    h ∈ torusGroup τ K := by
  have hconj : ∀ y, (∀ γ, IsRoot τ γ →
      y ∈ Subgroup.normalizer (rootSubgroup τ K γ : Set (ModGL τ K))) →
      ∀ S : Set (Fin τ.rank → ℤ), (∀ γ ∈ S, IsRoot τ γ) →
        ∀ x ∈ rootSpan τ K S, y * x * y⁻¹ ∈ rootSpan τ K S := by
    intro y hy S hS x hx
    have hle : rootSpan τ K S ≤ (rootSpan τ K S).comap (MulAut.conj y).toMonoidHom :=
      iSup₂_le fun γ hγ z hz => le_iSup₂_of_le (f := fun β (_ : β ∈ S) => rootSubgroup τ K β) γ hγ
        le_rfl ((Subgroup.mem_normalizer_iff.1 (hy γ (hS γ hγ)) z).1 hz)
    exact hle hx
  have hNi : ∀ γ, IsRoot τ γ →
      h⁻¹ ∈ Subgroup.normalizer (rootSubgroup τ K γ : Set (ModGL τ K)) :=
    fun γ hγ => inv_mem (hN γ hγ)
  have hnorm : ∀ S : Set (Fin τ.rank → ℤ), (∀ γ ∈ S, IsRoot τ γ) →
      h ∈ Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) := by
    intro S hS
    refine Subgroup.mem_normalizer_iff.2 fun x => ⟨hconj h hN S hS x, fun hx => ?_⟩
    have h1 := hconj h⁻¹ hNi S hS _ hx
    rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at h1
  have hB : h ∈ borelGroup τ K := by
    rw [← (borel_self_normalizers τ K).1]
    exact Subgroup.mem_inf.2 ⟨hh, hnorm _ fun _ hγ => hγ.1⟩
  have hB' : h ∈ oppositeBorel τ K := by
    rw [← oppositeBorel_normalizer]
    exact Subgroup.mem_inf.2 ⟨hh, hnorm _ fun _ hγ => hγ.1⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  rw [← (opposite_Borel_intersection τ K w₀ hw₀).2.2.1]
  exact Subgroup.mem_inf.2 ⟨hB, hB'⟩

end CFSG.StandardType.KGCentExc

end

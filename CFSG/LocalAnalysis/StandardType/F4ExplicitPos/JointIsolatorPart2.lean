module

public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Orbit
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointIsolatorPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.JointIsolator
open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups CFSG.StandardType.TableCRes
  CFSG.LieType.Steinberg.Adjoint Matrix
open Classical
variable {τ : Tag}

theorem exists_componentRoots_eq_of_kernelRoots_inter_component
    {τ : Tag} {M M' M'' : Type*} [CommGroup M] [CommGroup M']
        [CommGroup M'']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    {χ'' : Multiplicative (Fin τ.rank → ℤ) →* M''}
    (hsub : kernelRoots χ ⊆ kernelRoots χ')
    {j : KernelComponent χ'}
    (hker : kernelRoots χ'' = kernelRoots χ ∩ componentRoots χ' j)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots χ) (hγ' : γ ∈ componentRoots χ' j) :
    ∃ k : KernelComponent χ'',
      componentRoots χ'' k = componentRoots χ (⟦⟨γ, hγ⟩⟧ : KernelComponent χ) := by
  classical
  have hγ'' : γ ∈ kernelRoots χ'' := by
    rw [hker]
    exact ⟨hγ, hγ'⟩
  refine ⟨⟦⟨γ, hγ''⟩⟧, ?_⟩
  have hDsubC : componentRoots χ (⟦⟨γ, hγ⟩⟧ : KernelComponent χ) ⊆ componentRoots χ' j :=
    componentRoots_subset_of_kernel_subset hsub ⟨hγ, rfl⟩ hγ'
  have hsub'' : kernelRoots χ'' ⊆ kernelRoots χ := by
    intro z hz
    rw [hker] at hz
    exact hz.1
  refine Set.Subset.antisymm ?_ ?_
  · exact componentRoots_subset_of_kernel_subset hsub'' ⟨hγ'', rfl⟩ ⟨hγ, rfl⟩
  · intro x hxD
    have hx : x ∈ kernelRoots χ := hxD.1
    have hclass : (⟦⟨x, hx⟩⟧ : KernelComponent χ) = ⟦⟨γ, hγ⟩⟧ := hxD.2
    have hpathχ_sub : Relation.ReflTransGen (fun u v : kernelRoots χ =>
        (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0)
        ⟨γ, hγ⟩ ⟨x, hx⟩ := by
      have := kerRel_symm χ
      rw [← Relation.EqvGen.eqvGen_eq_reflTransGen]
      exact Quotient.exact hclass.symm
    have hpathχ_vec : Relation.ReflTransGen (KerAdjV χ) γ x :=
      reflTransGen_kerAdjV_of_reflTransGen χ hpathχ_sub
    have hS : ∀ ⦃a : Fin τ.rank → ℤ⦄, a ∈ kernelRoots χ'' →
        ∀ ⦃b : Fin τ.rank → ℤ⦄, KerAdjV χ a b → b ∈ kernelRoots χ'' := by
      intro a ha b hab
      rw [hker] at ha ⊢
      have hDaC : componentRoots χ (⟦⟨a, ha.1⟩⟧ : KernelComponent χ) ⊆ componentRoots χ' j :=
        componentRoots_subset_of_kernel_subset hsub ⟨ha.1, rfl⟩ ha.2
      have hbDa : b ∈ componentRoots χ (⟦⟨a, ha.1⟩⟧ : KernelComponent χ) := by
        refine ⟨hab.2.1, ?_⟩
        have hba : iform b a ≠ 0 := by
          rw [iform_comm]
          exact hab.2.2
        refine Quotient.sound (Relation.EqvGen.rel
          (r := fun u v : kernelRoots χ =>
            (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0)
          ⟨b, hab.2.1⟩ ⟨a, ha.1⟩ ?_)
        show (b : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (a : Fin τ.rank → ℤ)) ≠ 0
        rw [dotProduct_mulVec_eq_iform]
        exact hba
      exact ⟨hab.2.1, hDaC hbDa⟩
    obtain ⟨hx'', hpathS⟩ := reflTransGen_restrict hS hγ'' hpathχ_vec
    refine ⟨hx'', ?_⟩
    have hpath_sub'' : Relation.ReflTransGen (fun u v : kernelRoots χ'' =>
        (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0)
        ⟨γ, hγ''⟩ ⟨x, hx''⟩ :=
      reflTransGen_map (fun p : {a : Fin τ.rank → ℤ // a ∈ kernelRoots χ''} =>
          (⟨p.1, p.2⟩ : kernelRoots χ''))
        (fun p q hpq => by rw [dotProduct_mulVec_eq_iform]; exact hpq.2.2) hpathS
    exact (Quotient.sound (eqvGen_of_reflTransGen hpath_sub'')).symm

theorem kernelRoots_weylTuple
    {K : Type} [Field K] (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) :
    kernelRoots (rootCharHom (weylTuple w b)) =
      (fun α => w • α) '' kernelRoots (rootCharHom b) := by
  ext α
  rw [kernelRoots_rootCharHom]
  constructor
  · rintro ⟨hroot, hchar⟩
    refine ⟨w⁻¹ • α, ⟨?_, ?_⟩, ?_⟩
    · exact (isRoot_smul_iff w⁻¹).2 hroot
    · rw [rootChar_weylTuple] at hchar
      exact hchar
    · exact smul_inv_smul w α
  · rintro ⟨β, ⟨hβroot, hβchar⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact IsRoot.smul hβroot w
    · rw [rootChar_weylTuple, inv_smul_smul]
      exact hβchar

end CFSG.StandardType.F4ExplicitPos.JointIsolator

end

end

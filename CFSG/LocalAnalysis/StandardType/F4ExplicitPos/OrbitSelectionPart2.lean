module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang.Family
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OrbitSelectionPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.OrbitSelection
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.Assembly
open CFSG.LieType.Steinberg.Adjoint
open Matrix
open scoped commutatorElement
variable {τ : Tag} {L : Type} [Field L]

theorem component_le_rationalRootSpan
    (D : LangDatum τ L) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ)
    [Finite D.model]
    (a : Fin τ.rank → Lˣ) (ha : rootDiagUnit τ a ∈ D.torus)
    (hgen : toralCentralizer τ L a ≤
      torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hcomm : ∀ i j : KernelComponent (rootCharHom a), i ≠ j →
      ∀ u ∈ componentRootSpan L (rootCharHom a) i,
      ∀ v ∈ componentRootSpan L (rootCharHom a) j, Commute u v)
    (K : Subgroup (ModGL τ L))
    (hK : IsComponentOf K (D.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})) :
    ∃ i : KernelComponent (rootCharHom a),
      K ≤ rootSpan τ L (rationalRoots ρ (rootCharHom a) i) := by
  classical
  set χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ := rootCharHom a with hχ
  have hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ := by
    rintro γ ⟨hγroot, hγχ⟩
    refine ⟨(hρ.isRoot_iff γ).2 hγroot, ?_⟩
    show rootChar a (ρ γ) = 1
    have hγ1 : rootChar a γ = 1 := hγχ
    rw [hρ.rootChar_eq a ha γ hγroot, hγ1, one_pow]
  have hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ := hρ.iform_eq
  have hΓle : D.Γ ≤ D.model := Subgroup.commutator_le_self D.model
  have hΓ : D.Γ ≤ adjointGroup τ L := hΓle.trans inf_le_left
  have hΓfix : ∀ x ∈ D.Γ, D.step x = x := fun x hx => (hΓle hx).2
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.2.2.1⟩
  have hKmodel : K ≤ D.model := (hK.1.trans inf_le_left).trans hΓle
  have : Finite D.model := ‹Finite D.model›
  have : Finite ↥K :=
    Finite.of_injective (Subgroup.inclusion hKmodel) (Subgroup.inclusion_injective _)
  have hKadj : K ≤ toralCentralizer τ L a := fun x hx => ⟨hΓ (hK.1 hx).1, (hK.1 hx).2⟩
  have hKU : K ≤ rootSpan τ L (kernelRoots χ) :=
    perfect_le_kernelRootSpan a hgen hKadj hKperf
  have : Finite (kernelRoots χ) := ((finite_setOf_isRoot τ).subset fun α h => h.1).to_subtype
  have : Finite (KernelComponent χ) := inferInstance
  have : Finite (Set.range (rationalRoots ρ χ)) := (Set.finite_range _).to_subtype
  let A : Set.range (rationalRoots ρ χ) → Subgroup (ModGL τ L) := fun O => rootSpan τ L O.1
  have hc : ∀ O O', O ≠ O' → ∀ x ∈ A O, ∀ y ∈ A O', Commute x y := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hne
    exact orbit_commute_rootSpan_rationalRoots hcomm hker hform (fun h => hne (Subtype.ext h))
  have hF : ∀ O, ∀ x ∈ A O, D.step x ∈ A O := by
    rintro ⟨_, i, rfl⟩ x hx
    exact orbit_step_mem_rootSpan D hρ
      (fun γ hγ => (orbit_rationalRoots_subset_kernelRoots hker i hγ).1)
      (orbit_rationalRoots_mapsTo i) hx
  have hU : ⨆ O, A O = rootSpan τ L (kernelRoots χ) := by
    refine le_antisymm (iSup_le fun O => ?_) ?_
    · obtain ⟨_, i, rfl⟩ := O
      exact rootSpan_mono (orbit_rationalRoots_subset_kernelRoots hker i)
    · refine le_trans (iSup_componentRootSpan L (χ := χ)).ge (iSup_le fun i => ?_)
      have h : componentRootSpan L χ i ≤ A ⟨_, i, rfl⟩ :=
        rootSpan_mono fun γ hγ => ⟨0, γ, hγ, rfl⟩
      exact h.trans (le_iSup A ⟨_, i, rfl⟩)
  have hAadj : ∀ O, A O ≤ adjointGroup τ L := fun O => rootSpan_le_adjointGroup L O.1
  have h1 := perfect_le_iSup_inf_fixed D.step A hc hF hKperf (hKU.trans hU.ge)
    fun x hx => hΓfix x (Subgroup.mem_inf.1 (hK.1 hx)).1
  have hc2 : ∀ O O', O ≠ O' → ∀ x ∈ A O ⊓ D.step.eqLocus (MonoidHom.id _),
      ∀ y ∈ A O' ⊓ D.step.eqLocus (MonoidHom.id _), Commute x y :=
    fun O O' hne x hx y hy => hc O O' hne x hx.1 y hy.1
  have h2 : K ≤ ⨆ O, A O ⊓ D.Γ := by
    refine (perfect_le_iSup_commutator (fun O => A O ⊓ D.step.eqLocus (MonoidHom.id _)) hc2
      hKperf h1).trans (iSup_mono fun O => le_inf ?_ ?_)
    · exact (Subgroup.commutator_mono inf_le_left inf_le_left).trans
        (Subgroup.commutator_le_self _)
    · exact Subgroup.commutator_mono (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
        (fun x hx => ⟨hAadj O hx.1, hx.2⟩)
  have hker₁ : ∀ i γ, γ ∈ rationalRoots ρ χ i → rootChar a γ = 1 := by
    intro i γ hγ
    exact (orbit_rationalRoots_subset_kernelRoots hker i hγ).2
  have hcent : ∀ O, A O ≤ Subgroup.centralizer {rootDiagUnit τ a} := by
    rintro ⟨_, i, rfl⟩ x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (Subgroup.mem_centralizer_iff.1 (rootSpan_le_centralizer a
      (fun γ hγ => ⟨(orbit_rationalRoots_subset_kernelRoots hker i hγ).1, hker₁ i γ hγ⟩)
      hx)) _ (Set.mem_singleton _)
  set P' : Subgroup (ModGL τ L) := ⨆ O, A O ⊓ D.Γ with hP'
  have hP'X : P' ≤ D.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} :=
    iSup_le fun O => le_inf inf_le_right (inf_le_left.trans (hcent O))
  have hKP' : K ≤ P' := h2
  have : Finite ↥P' := Finite.of_injective
    (Subgroup.inclusion (((hP'X.trans inf_le_left).trans hΓle) : P' ≤ D.model))
    (Subgroup.inclusion_injective _)
  have hKcomp : IsComponentOf K P' :=
    ⟨hKP', isSubnormal_of_le_of_le' hK.2.1 hKP' hP'X, hK.2.2⟩
  have hnorm : ∀ O, ((A O ⊓ D.Γ).subgroupOf P').Normal := by
    intro O
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_iSup (fun O => A O ⊓ D.Γ) O)]
    refine iSup_le fun O' => ?_
    by_cases hOO : O' = O
    · rw [hOO]; exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (A O ⊓ D.Γ : Set (ModGL τ L)))
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hc O O' (Ne.symm hOO) y hy.1 x hx.1).eq
  have hsub : ∀ O, IsSubnormal (A O ⊓ D.Γ) P' := fun O =>
    IsSubnormal.step (le_iSup (fun O => A O ⊓ D.Γ) O) (hnorm O) (IsSubnormal.refl P')
  have hex : ∃ O, K ≤ A O ⊓ D.Γ := by
    by_contra hcon
    push Not at hcon
    have hcomm' : ∀ O, ⁅K, A O ⊓ D.Γ⁆ = ⊥ := fun O =>
      (comp_le_or_commutator_eq_bot hKcomp (hsub O)).resolve_left (hcon O)
    have hP'c : P' ≤ Subgroup.centralizer (K : Set (ModGL τ L)) :=
      iSup_le fun O => Subgroup.commutator_eq_bot_iff_le_centralizer.1
        ((Subgroup.commutator_comm _ _).trans (hcomm' O))
    have hKc : K ≤ Subgroup.centralizer (K : Set (ModGL τ L)) := hKP'.trans hP'c
    obtain ⟨x, y, hxy⟩ := exists_noncomm_of_isQuasisimple hK.2.2
    exact hxy (Subtype.ext (Subgroup.mem_centralizer_iff.1 (hKc y.2) x x.2))
  obtain ⟨⟨_, i, rfl⟩, hKi⟩ := hex
  exact ⟨i, hKi.trans inf_le_left⟩

end CFSG.StandardType.F4ExplicitPos.OrbitSelection

end

end

module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UF4
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart5

@[expose] public section

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TableCRes CFSG.StandardType.LieCore
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.F4ExplicitPos.JointRankOrbit

theorem componentRoots_image_eq_of_rank_ge_two
    {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)}
    (hρR : ∀ γ, IsRoot Tag.F4 (ρ γ) ↔ IsRoot Tag.F4 γ)
    (hρ : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ)
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (i : KernelComponent χ)
    (h2 : 2 ≤ compRank (componentRoots χ i)) :
    (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) '' componentRoots χ i =
      componentRoots χ i := by
  classical
  obtain ⟨j, hj⟩ := exists_image_component_of_stable χ hker hρ i
  by_contra hne
  have hij : i ≠ j := by
    rintro rfl
    exact hne hj
  have hΨ : IsRootComponent (componentRoots χ i) := isRootComponent_componentRoots i
  have horth : ∀ γ ∈ componentRoots χ i,
      ∀ δ ∈ (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) '' componentRoots χ i,
      iform γ δ = 0 ∧ ¬ IsRoot Tag.F4 (γ + δ) := by
    intro γ hγ δ hδ
    have hδj : δ ∈ componentRoots χ j := by
      rw [← hj]
      exact hδ
    refine ⟨iform_eq_zero_of_mem_componentRoots' hij hγ hδj, ?_⟩
    have hmk : (⟦⟨γ, hγ.1⟩⟧ : KernelComponent χ) ≠ ⟦⟨δ, hδj.1⟩⟧ := by
      rw [hγ.2, hδj.2]
      exact hij
    have hnr := not_isRoot_of_mk_ne (χ := χ) hmk (a := 1) (b := 1)
      (by norm_num) (by norm_num)
    simpa using hnr
  have hle := f4_finrank_le_one hΨ hρR hρ horth
  have hfin : (componentRoots χ i).Finite :=
    (finite_setOf_isRoot Tag.F4).subset fun γ hγ => hγ.1.1
  have hrank := CFSG.StandardType.F4ExplicitPos.RankOrbit.finrank_span_eq_compRank
    (τ := Tag.F4) (componentRoots χ i) hfin
  rw [hrank] at hle
  omega

theorem f4_cyclic_componentOrbitLength_eq_one_of_rank_ge_two
    {L : Type} [Field L]
    (D : LangDatum Tag.F4 L) (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ))
    (hρ : FrobRootMap D ρ)
    (a : Fin Tag.F4.rank → Lˣ) (ha : rootDiagUnit Tag.F4 a ∈ D.torus)
    (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i)) :
    (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i ∧
      componentOrbitLength ρ (componentRoots (rootCharHom a) i) = 1 := by
  have hker : ∀ γ ∈ kernelRoots (rootCharHom a), ρ γ ∈ kernelRoots (rootCharHom a) := by
    rintro γ ⟨hγroot, hγ⟩
    have hγ' : rootChar a γ = 1 := hγ
    refine ⟨(hρ.isRoot_iff γ).2 hγroot, ?_⟩
    show rootChar a (ρ γ) = 1
    rw [hρ.rootChar_eq a ha γ hγroot, hγ', one_pow]
  have heq := componentRoots_image_eq_of_rank_ge_two hρ.isRoot_iff hρ.iform_eq hker i h2
  refine ⟨heq, ?_⟩
  refine componentOrbitLength_eq_one ?_ ?_
  · exact (finite_setOf_isRoot Tag.F4).subset fun γ hγ => hγ.1.1
  · intro γ hγ
    rw [← heq]
    exact ⟨γ, hγ, rfl⟩

end CFSG.StandardType.F4ExplicitPos.JointRankOrbit

end

end

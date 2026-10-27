module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
import CFSG.LocalAnalysis.StandardType.GGLieCoreCentOrbit
import CFSG.LocalAnalysis.StandardType.ExcPos.ContainingComponent
import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ratOrbit_mono {τ : Tag} (ρ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    {Ψ Ψ' : Set (Fin τ.rank → ℤ)} (h : Ψ ⊆ Ψ') :
    LieCore.ratOrbit ρ Ψ ⊆ LieCore.ratOrbit ρ Ψ' := by
  rintro γ ⟨k, δ, hδ, rfl⟩
  exact ⟨k, δ, h hδ, rfl⟩

theorem kernelRoots_jointChar_self_subset {τ : Tag} {L : Type} [Field L]
    (a : Fin τ.rank → Lˣ) :
    kernelRoots (LieCore.jointChar a a) ⊆
      kernelRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) := by
  rintro γ ⟨hroot, hχ⟩
  have hχ' : (CFSG.LieType.AlgebraicGroups.rootCharHom a (Multiplicative.ofAdd γ),
      CFSG.LieType.AlgebraicGroups.rootCharHom a (Multiplicative.ofAdd γ)) = 1 := hχ
  exact ⟨hroot, (Prod.mk_eq_one.1 hχ').1⟩

theorem exists_component_le_ratOrbitSpan_single
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap D ρ) (hfin : Finite D.model)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : Fin τ.rank → Lˣ)
    (ha : rootDiagUnit τ a ∈ D.torus) (hap : rootDiagUnit τ a ^ p = 1)
    (K : Subgroup (ModGL τ L))
    (hK : CFSG.Assembly.IsComponentOf K (D.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a})) :
    ∃ j : KernelComponent (CFSG.LieType.AlgebraicGroups.rootCharHom a),
      K ≤ rootSpan τ L (LieCore.ratOrbit ρ
        (componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) j)) := by
  have hK' : CFSG.Assembly.IsComponentOf K (D.Γ ⊓ Subgroup.centralizer
      ((Subgroup.closure {rootDiagUnit τ a, rootDiagUnit τ a} : Subgroup (ModGL τ L)) :
        Set (ModGL τ L))) := by
    rw [Set.pair_eq_singleton, Subgroup.centralizer_closure]
    exact hK
  obtain ⟨i, hi⟩ := LieCore.ggLieCentOrbit_component_le_orbitSpan D ρ hρ hfin hp hp2
    a a ha ha hap hap K hK'
  refine ⟨containingComponent (kernelRoots_jointChar_self_subset a) i, ?_⟩
  refine hi.trans (rootSpan_mono ?_)
  exact ratOrbit_mono ρ (componentRoots_subset_containingComponent _ i)

end CFSG.StandardType.LieKnownR2.ExcPos

end

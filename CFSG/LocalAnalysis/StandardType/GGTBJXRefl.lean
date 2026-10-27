module

public import CFSG.LocalAnalysis.StandardType.GGTBJXDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJXRoots
public import CFSG.LocalAnalysis.StandardType.GGTBJXReflAux

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggTBJX_refl
    {τ : Tag} {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {ζ : Kˣ}
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* ModGL τ K}
    {σ : Multiplicative (Fin τ.rank → ZMod p) →* L'} (hstd : GGTBJXStd p τ ζ ψ σ)
    (f₀ : Multiplicative (Fin τ.rank → ZMod p)) {J : Subgroup L'}
    (i : KernelComponent (rootCharHom (ggTBJXa p τ ζ f₀)))
    (hJi : J.map ψ = componentRootSpan K (rootCharHom (ggTBJXa p τ ζ f₀)) i)
    {β : Fin τ.rank → ℤ}
    (hβ : β ∈ componentRoots (rootCharHom (ggTBJXa p τ ζ f₀)) i) :
    ∃ m ∈ J, ∀ f : Multiplicative (Fin τ.rank → ZMod p),
      ψ m * ψ (σ f) * (ψ m)⁻¹ = ψ (σ (ggTBJXReflAut p τ β f)) := by
  classical
  have hβroot : IsRoot τ β := isRoot_of_mem_componentRoots hβ
  obtain ⟨n, hn_mem, hn_conj⟩ := ggTBJ_exists_weylElt (τ := τ) (K := K) hβroot
  have hnβ : n ∈ componentRootSpan K (rootCharHom (ggTBJXa p τ ζ f₀)) i := by
    refine rootSpan_mono ?_ hn_mem
    intro α hα
    rcases hα with rfl | rfl
    · exact hβ
    · exact (isRootComponent_componentRoots i).neg_mem β hβ
  have hnJ : n ∈ J.map ψ := by
    rw [hJi]
    exact hnβ
  obtain ⟨m, hmJ, hψm⟩ := Subgroup.mem_map.mp hnJ
  refine ⟨m, hmJ, fun f => ?_⟩
  have hζ : orderOf ζ = p := hstd.2.2.1
  have hfunvec : ggTBJXFun p τ β (ggTBJXVec p τ β) = 2 := ggTBJX_fun_vec_self p hβroot
  rw [hψm, hstd.2.2.2 f, hstd.2.2.2 (ggTBJXReflAut p τ β f)]
  rw [hn_conj (ggTBJXa p τ ζ f)]
  exact congrArg (rootDiagUnit τ) (ggTBJX_ggTBJXa_refl p ζ hζ hfunvec f)

end CFSG.StandardType

end

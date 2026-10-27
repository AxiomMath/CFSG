module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4Defs
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Weyl
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Roots
public import CFSG.LocalAnalysis.StandardType.GGTBJF4ReflAux

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggTBJ_f4_refl
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] {ζ : Kˣ}
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* ModGL Tag.F4 K}
    {σ : Multiplicative (Fin 4 → ZMod p) →* L'} (hstd : GGTBJF4Std p ζ ψ σ)
    (f₀ : Multiplicative (Fin 4 → ZMod p)) {J : Subgroup L'}
    (i : KernelComponent (rootCharHom (ggTBJa p ζ f₀)))
    (hJi : J.map ψ = componentRootSpan K (rootCharHom (ggTBJa p ζ f₀)) i)
    {β : Fin 4 → ℤ} (hβ : β ∈ componentRoots (rootCharHom (ggTBJa p ζ f₀)) i) :
    ∃ m ∈ J, ∀ f : Multiplicative (Fin 4 → ZMod p),
      ψ m * ψ (σ f) * (ψ m)⁻¹ = ψ (σ (ggTBJReflAut p β f)) := by
  classical
  have hβroot : IsRoot Tag.F4 β := isRoot_of_mem_componentRoots hβ
  obtain ⟨n, hn_mem, hn_conj⟩ := ggTBJ_exists_weylElt (τ := Tag.F4) (K := K) hβroot
  have hnβ : n ∈ componentRootSpan K (rootCharHom (ggTBJa p ζ f₀)) i := by
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
  have hfunvec : ggTBJFun p β (ggTBJVec p β) = 2 := ggTBJ_fun_vec_self p hβroot
  rw [hψm, hstd.2.2.2 f, hstd.2.2.2 (ggTBJReflAut p β f)]
  rw [hn_conj (ggTBJa p ζ f)]
  exact congrArg (rootDiagUnit Tag.F4) (ggTBJ_ggTBJa_refl p ζ hζ hfunvec f)

end CFSG.StandardType

end


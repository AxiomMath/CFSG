module

public import CFSG.LocalAnalysis.StandardType.PhanEAdjFrob
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.StandardType.AutSt
open CFSG.ClassicalInvolution.Models.TwistedPairs (involEquiv)

variable {τ : Tag} {k₀ k : Type} [Field k₀] [Field k]

private theorem q2nPE_baseChangeGL_eltUnit (F : RootOperatorFamily τ) (ι : k₀ →+* k)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : k₀) :
    baseChangeGL (τ := τ) ι (F.eltUnit k₀ ⟨γ, hγ⟩ c) = F.eltUnit k ⟨γ, hγ⟩ (ι c) := by
  refine Units.ext ?_
  change (baseChangeEndHom ι (F.elt k₀ ⟨γ, hγ⟩ c) : Module.End k (RootModule τ k)) =
    F.elt k ⟨γ, hγ⟩ (ι c)
  change baseChangeEnd (τ := τ) ι (F.elt k₀ ⟨γ, hγ⟩ c) = F.elt k ⟨γ, hγ⟩ (ι c)
  exact (baseChange_baseChangeEnd ι (F.elt k₀ ⟨γ, hγ⟩ c)).unique
    (BaseChange.elt F ⟨γ, hγ⟩ c)

theorem adjBC_xPar (ι : k₀ →+* k) (γ : Fin τ.rank → ℤ) (c : k₀) :
    adjointBaseChangeHom τ ι (xPar (rootOperatorFamily τ) γ c) =
      xPar (rootOperatorFamily τ) γ (ι c) := by
  by_cases hγ : IsRoot τ γ
  · apply Subtype.ext
    rw [coe_adjointBaseChangeHom, xPar_of_isRoot hγ, xPar_of_isRoot hγ,
      RootOperatorFamily.coe_eltElement, RootOperatorFamily.coe_eltElement]
    exact q2nPE_baseChangeGL_eltUnit (rootOperatorFamily τ) ι hγ c
  · rw [xPar_of_not_isRoot hγ, xPar_of_not_isRoot hγ, map_one]

theorem adjBC_fixed (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (ι : k₀ →+* k)
    (hι : ∀ c, θ (ι c) = ι c) (y : adjointGroup τ k₀) :
    entrywiseAdjointAut τ (involEquiv θ hθ) (adjointBaseChangeHom τ ι y) =
      adjointBaseChangeHom τ ι y := by
  have htop : (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ},
      rootGroup (rootOperatorFamily τ) k₀ γ.1) = ⊤ := by
    rw [iSup_subtype]
    exact iSup_rootGroup_eq_top (rootOperatorFamily τ) k₀
  have hle : (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ},
      rootGroup (rootOperatorFamily τ) k₀ γ.1) ≤
      MonoidHom.eqLocus
        ((entrywiseAdjointAut τ (involEquiv θ hθ)).toMonoidHom.comp
          (adjointBaseChangeHom τ ι)) (adjointBaseChangeHom τ ι) := by
    refine iSup_le fun γ => ?_
    rintro x hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff γ.2 x).1 hx
    change (entrywiseAdjointAut τ (involEquiv θ hθ)).toMonoidHom
        (adjointBaseChangeHom τ ι (xPar (rootOperatorFamily τ) γ.1 c)) =
      adjointBaseChangeHom τ ι (xPar (rootOperatorFamily τ) γ.1 c)
    rw [show (entrywiseAdjointAut τ (involEquiv θ hθ)).toMonoidHom
          (adjointBaseChangeHom τ ι (xPar (rootOperatorFamily τ) γ.1 c)) =
        entrywiseAdjointAut τ (involEquiv θ hθ)
          (adjointBaseChangeHom τ ι (xPar (rootOperatorFamily τ) γ.1 c)) from rfl,
      adjBC_xPar ι γ.1 c, adj_phi_xPar θ hθ γ.1 (ι c), hι c]
  have hy : y ∈ (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ},
      rootGroup (rootOperatorFamily τ) k₀ γ.1) := by
    rw [htop]
    exact Subgroup.mem_top y
  exact hle hy

theorem adjBC_descent_rootGroup (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (ι : k₀ →+* k)
    (hdesc : ∀ c, θ c = c → ∃ c', ι c' = c) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {x : adjointGroup τ k} (hx : x ∈ rootGroup (rootOperatorFamily τ) k γ)
    (hfix : entrywiseAdjointAut τ (involEquiv θ hθ) x = x) :
    x ∈ (adjointBaseChangeHom τ ι).range := by
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
  have hc : θ c = c := xPar_injective hγ (by
    rw [← adj_phi_xPar θ hθ γ c]
    exact hfix)
  obtain ⟨c', hc'⟩ := hdesc c hc
  exact ⟨xPar (rootOperatorFamily τ) γ c', by rw [adjBC_xPar ι γ c', hc']⟩

end CFSG.ClassicalInvolution.Phan.PhanE

module

public import CFSG.LocalAnalysis.StandardType.GGLangRatStep
public import CFSG.LocalAnalysis.StandardType.GGLangCoroot
public import CFSG.LocalAnalysis.StandardType.GGLangModelIndex

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem rootSL2_WSL_mem_Γ_of_rho
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hq : S.D.q = 2 ^ f) (hAlg : S.IsAlgebraic)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hρα : S.ρ α = α ∨ S.ρ α = -α) :
    rootSL2 τ L α WSL ∈ S.Γ := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S hq
  refine langModel_mem_Γ_of_sq_eq_one S hτ hq hAlg
    (rootSL2_WSL_mem_model_of_rho S hα hρα) ?_
  rw [pow_two]
  exact rootSL2_WSL_mul_self α

theorem rootSL2_HSL_mem_rationalComponent_of_entrywise_step'
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hq : S.D.q = 2 ^ f) (hAlg : S.IsAlgebraic) {Fr : L →+* L} {w : WeylGroup τ}
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w)
    (hw : ∀ v : Fin τ.rank → ℤ, w • v = -v)
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i)
    (hργ : S.ρ γ = γ ∨ S.ρ γ = -γ)
    {t : Lˣ} (ht : Units.map Fr.toMonoidHom t = t⁻¹)
    {m : ℕ} (hm : Odd m) (htm : t ^ m = 1) :
    rootSL2 τ L γ (HSL t) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S hq
  have hγr : IsRoot τ γ := (isRootComponent_componentRoots i).isRoot γ hγ
  exact rootSL2_HSL_mem_rationalComponent_of_entrywise_step S hΦ hn hw i hγ
    (rootSL2_WSL_mem_Γ_of_rho S hτ hq hAlg hγr hργ) ht hm htm

end CFSG.StandardType.LangRat

end

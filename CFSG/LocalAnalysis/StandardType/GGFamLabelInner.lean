module

public import CFSG.LocalAnalysis.StandardType.GGFamInnerDispatch
public import CFSG.LocalAnalysis.StandardType.GGFamLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelKind

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint

theorem langFamRatLabel_inner
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hnA : ¬ (1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)) :
    FamLabelAt S (famCharHom a) i := by
  obtain ⟨-, t, n, f, hmodel, hpow, hP⟩ :=
    fam_inner_nonA_strongRecogIn hτ S hp hT hap h1 i hnA hinner
  have hf1 : 1 ≤ f := hmodel.admissible.2.1
  refine ⟨f, hpow, ?_⟩
  rw [twistKindOf_eq_inner_of_twistInner S.ρ _ hinner]
  rcases hP with ⟨rfl, rfl, h4, hN⟩ | ⟨rfl, rfl, hr, hN⟩ | ⟨rfl, rfl, hr, hN⟩ |
    ⟨rfl, rfl, hr, hN⟩
  · rw [componentLabel_inner_D f h4 hN]
    exact ggCompLabelAt_D _ f h4 hf1 hmodel
  · rw [hr, show (componentRoots (famCharHom a) i).ncard = 72 by rw [hN, hr]; rfl,
      componentLabel_inner_E6 f rfl]
    exact ggCompLabelAt_E6 f hf1 hmodel
  · rw [hr, show (componentRoots (famCharHom a) i).ncard = 126 by rw [hN, hr]; rfl,
      componentLabel_inner_E7 f rfl]
    exact ggCompLabelAt_E7 f hf1 hmodel
  · rw [hr, show (componentRoots (famCharHom a) i).ncard = 240 by rw [hN, hr]; rfl,
      componentLabel_inner_E8 f rfl]
    exact ggCompLabelAt_E8 f hf1 hmodel

end CFSG.StandardType.TableCRes

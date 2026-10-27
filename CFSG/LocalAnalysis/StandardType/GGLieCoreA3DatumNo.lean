module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DatumDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

theorem ggLieA3DatumNo_of_lattice
    (h : GGLieA3LatticeNo) : GGLieA3DatumNo := by
  intro t ht hΦ w g hg hlang a₁ a₂ ρ i hyp
  obtain ⟨hρ, hT₁, hT₂, hp₁, hp₂, hcard, _, hnc, himg, hin⟩ := hyp
  have ht' : t = .E6 ∨ t = .F4 ∨ t = .twistedE6 :=
    ht.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))
  have h3₁ : ∀ i, a₁ i ^ 3 = 1 := by
    have h : a₁ ^ 3 = 1 :=
      rootDiagUnit_injective (by rw [← rootDiagUnit_pow, hp₁, rootDiagUnit_one])
    intro i
    simpa using congrFun h i
  have h3₂ : ∀ i, a₂ i ^ 3 = 1 := by
    have h : a₂ ^ 3 = 1 :=
      rootDiagUnit_injective (by rw [← rootDiagUnit_pow, hp₂, rootDiagUnit_one])
    intro i
    simpa using congrFun h i
  have hq : (langDatumOfPosition hΦ w g hg hlang).q = 2 := rfl
  have hchar₁ : ∀ γ, IsRoot (langTag t) γ →
      rootChar a₁ (w • ggGraphLat t γ) = rootChar a₁ γ ^ 2 := by
    intro γ hγ
    have hfrob : ρ γ = w • ggGraphLat t γ :=
      ggLie_frobRootMap_eq_on_roots ht' (f := 1) (le_refl 1) hΦ w g hg hlang hρ hγ
    have h1 : rootChar a₁ (w • ggGraphLat t γ) = rootChar a₁ (ρ γ) := by rw [hfrob]
    rw [h1, hρ.rootChar_eq a₁ hT₁ γ hγ, hq]
  have hchar₂ : ∀ γ, IsRoot (langTag t) γ →
      rootChar a₂ (w • ggGraphLat t γ) = rootChar a₂ γ ^ 2 := by
    intro γ hγ
    have hfrob : ρ γ = w • ggGraphLat t γ :=
      ggLie_frobRootMap_eq_on_roots ht' (f := 1) (le_refl 1) hΦ w g hg hlang hρ hγ
    have h1 : rootChar a₂ (w • ggGraphLat t γ) = rootChar a₂ (ρ γ) := by rw [hfrob]
    rw [h1, hρ.rootChar_eq a₂ hT₂ γ hγ, hq]
  have himg' : (fun u => w • ggGraphLat t u) '' componentRoots (jointChar a₁ a₂) i =
      componentRoots (jointChar a₁ a₂) i := by
    have hcongr : (fun u => ρ u) '' componentRoots (jointChar a₁ a₂) i =
        (fun u => w • ggGraphLat t u) '' componentRoots (jointChar a₁ a₂) i :=
      Set.image_congr fun γ hγ =>
        ggLie_frobRootMap_eq_on_roots ht' (f := 1) (le_refl 1) hΦ w g hg hlang hρ hγ.1.1
    exact hcongr.symm.trans himg
  have hin' : twistInner (componentRoots (jointChar a₁ a₂) i) (fun u => w • ggGraphLat t u) := by
    obtain ⟨z, hz, hzγ⟩ := hin
    refine ⟨z, hz, fun γ hγ => ?_⟩
    show w • ggGraphLat t γ = z • γ
    rw [← ggLie_frobRootMap_eq_on_roots ht' (f := 1) (le_refl 1) hΦ w g hg hlang hρ hγ.1.1]
    exact hzγ γ hγ
  exact h t ht w a₁ a₂ h3₁ h3₂ hchar₁ hchar₂ hcard i hnc himg' hin'

end CFSG.StandardType.LieCore

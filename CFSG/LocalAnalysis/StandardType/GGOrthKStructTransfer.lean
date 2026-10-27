module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs

import CFSG.LocalAnalysis.StandardType.StarFour.Dictionary
import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleBasic
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityLinear
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.StandardType.StarFour.CentralizerSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf
  CFSG.LieType.Universal.SpecialLinear Matrix

theorem ggOrthKStruct_transfer {G : Type} [Group G] {K J : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G} (hψr : ψ.range = K)
    (hψi : Function.Injective ψ) {x : G} {t : SpecialLinearGroup (Fin (n + 1)) F2}
    (hxt : ∀ l ∈ K, x * l * x⁻¹ = ψ t * l * (ψ t)⁻¹)
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({x} : Set G) ⊓ K))
    (hf : ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 f) :
    ∃ J' : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2),
      CFSG.Assembly.IsComponentOf J'
        (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2))) ∧
      ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel (↥J' ⧸ Subgroup.center ↥J') .PSL 4 2 f := by
  have hS : ∀ b ∈ ({x} : Set G), ∀ u : SpecialLinearGroup (Fin (n + 1)) F2,
      b * ψ u * b⁻¹ = ψ (t * u * t⁻¹) := by
    intro b hb u
    rw [Set.mem_singleton_iff] at hb
    subst hb
    rw [hxt (ψ u) (hψr ▸ MonoidHom.mem_range.mpr ⟨u, rfl⟩)]
    simp only [map_mul, map_inv]
  have hcent : Subgroup.centralizer ({x} : Set G) ⊓ K =
      (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2))).map ψ := by
    have h := CFSG.StandardType.StarFour.inf_centralizer_eq_map_centralizer ψ hψi
      ({x} : Set G) (fun _ : G => t) hS
    rw [Set.image_singleton] at h
    rw [← hψr, inf_comm]
    exact h
  have hJK : J ≤ K := hJ.1.trans inf_le_right
  have hJrange : J ≤ ψ.range := by
    rw [hψr]
    exact hJK
  have hKle : Subgroup.centralizer ({x} : Set G) ⊓ K ≤ ψ.range := by
    rw [hψr]
    exact inf_le_right
  have hJ'comp0 := CFSG.ComponentClassification.OddClassSelector.isComponentOf_comap_of_le_range
    ψ hψi hJ hKle
  have hcompeq : (Subgroup.centralizer ({x} : Set G) ⊓ K).comap ψ =
      Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2)) := by
    rw [hcent, Subgroup.comap_map_eq_self_of_injective hψi]
  have hJ'comp : CFSG.Assembly.IsComponentOf (J.comap ψ)
      (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2))) := by
    rw [hcompeq] at hJ'comp0
    exact hJ'comp0
  obtain ⟨f, hf2, hfmod⟩ := hf
  refine ⟨J.comap ψ, hJ'comp, f, hf2, ?_⟩
  have hmap : (J.comap ψ).map ψ = J := Subgroup.map_comap_eq_self hJrange
  have e : ↥(J.comap ψ) ≃* ↥J :=
    (Subgroup.equivMapOfInjective (J.comap ψ) ψ hψi).trans (MulEquiv.subgroupCongr hmap)
  have he : (Subgroup.center ↥(J.comap ψ)).map (e : ↥(J.comap ψ) →* ↥J) =
      Subgroup.center ↥J :=
    Subgroup.map_center_eq e
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center ↥(J.comap ψ)) (Subgroup.center ↥J) e he).symm hfmod

end CFSG.StandardType

end

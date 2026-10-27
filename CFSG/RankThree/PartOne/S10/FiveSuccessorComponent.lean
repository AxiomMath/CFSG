module

import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S10.FiveSuccessorTheta
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.GroupTheory.SteinbergBY CFSG.LocalAnalysis.ComponentInitial

theorem exists_theta_component_containing_five_residual (hS : SchreierFor InCatalog) {G : Type}
    [Group G] [Finite G] {A L : Subgroup G} {c e : G} (hS10 : SteinbergBM.SectionTenSetup G 5 A)
    (hcA : c ∈ A) (hc1 : c ≠ 1) (heA : e ∈ A) (he1 : e ≠ 1) (hLc : L ∈ thetaComponentsAt 5 c)
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (htriv : ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ inSubgroup (aschbacherSolvableCore 5) L) :
    ∃ K ∈ thetaComponentsAt 5 e, fiveResidual L e ≤ K ∧
      fiveResidual L e ≤ Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) ∧
      (fiveResidual L e).subgroupOf
        (Subgroup.centralizer ({e} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) ∈
        thetaComponents 5 ↥(Subgroup.centralizer ({e} : Set G) ⊓
          Subgroup.centralizer ({c} : Set G)) := by
  have hp : (5 : ℕ).Prime := by norm_num
  obtain ⟨hsimple, hnonab, hKP, -, -, -, hAe, -, -, -⟩ := id hS10
  have : IsSimpleGroup G := hsimple
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS10).le
  have hac : c * e = e * c := congrArg Subtype.val (hAe.is_comm.comm ⟨c, hcA⟩ ⟨e, heA⟩)
  have hordc : orderOf c = 5 :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hcA hc1
  have hordE : orderOf e = 5 :=
    EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp heA he1
  obtain ⟨-, P', hP', hP'eq⟩ := EmbeddingFixedResidual.fixed_residual_ambient hp hac
    ⟨1, by rw [pow_one]; exact hordE⟩ hLc (hAL heA) htriv
  have hHK : CFSG.IsKGroup (Subgroup.centralizer ({e} : Set G)) :=
    hKP _ (EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab he1)
  have hHE : evenRank (Subgroup.centralizer ({e} : Set G)) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans he
  have hc'ord : orderOf (⟨c, EmbeddingFixedResidual.commute_mem_centralizer hac⟩ :
      Subgroup.centralizer ({e} : Set G)) = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact hordc
  obtain ⟨K₀, hK₀, hPK⟩ := local_theta_component_embedding_frontier hS _ hHK hHE 5 hp
    (by norm_num) _ hc'ord P' hP'
  have hres : fiveResidual L e = P'.map (Subgroup.centralizer ({e} : Set G)).subtype := hP'eq.symm
  refine ⟨K₀.map (Subgroup.centralizer ({e} : Set G)).subtype, ⟨K₀, hK₀, rfl⟩,
    hres ▸ Subgroup.map_mono hPK, ?_⟩
  obtain ⟨T, hT, rfl⟩ := hP'
  have hZ := map_subtype_centralizer_singleton (Subgroup.centralizer ({e} : Set G))
    ⟨c, EmbeddingFixedResidual.commute_mem_centralizer hac⟩
  have h := map_mem_thetaComponents_subgroupOf_of_map_eq hp hZ hT
  rw [hP'eq] at h
  exact h

end CFSG.RankThree.PartOne

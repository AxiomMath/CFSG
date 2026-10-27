module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

theorem section_ten_trivial_actor_component_supplement_of
    (hnorm : SelectedPrimeElementsNormalizeThetaComponents)
    (hemb : LocalThetaComponentEmbeddingFrontier) :
    SectionTenTrivialActorComponentSupplement := by
  intro hS G _ _ _ hnonab hKP hE p hp hp3 A hA a haA ha1 L hL hLa
  have := hA
  obtain ⟨c, hcA, hc1, hLc⟩ := mem_thetaComponentFamily_iff.mp hL
  have hac : c * a = a * c := congrArg Subtype.val (hA.is_comm.comm ⟨c, hcA⟩ ⟨a, haA⟩)
  have hordA : orderOf a = p := EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp haA ha1
  have hordc : orderOf c = p := EmbeddingFixedResidual.orderOf_eq_of_isElementaryAbelian hp hcA hc1
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := hnorm.2 G hE p hp hp3 A hA L hL
  obtain ⟨hsup, P', hP', hP'eq⟩ := EmbeddingFixedResidual.fixed_residual_ambient hp hac
    ⟨1, by rw [pow_one]; exact hordA⟩ hLc (hAL haA)
    (EmbeddingFixedResidual.trivial_action_of_commutator_le hLa)
  have hHK : CFSG.IsKGroup (Subgroup.centralizer ({a} : Set G)) :=
    hKP _ (EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab ha1)
  have hHE : evenRank (Subgroup.centralizer ({a} : Set G)) ≤ 3 :=
    (Sec9A.evenRank_subgroup_le _).trans hE
  have hc'ord : orderOf (⟨c, EmbeddingFixedResidual.commute_mem_centralizer hac⟩ :
      Subgroup.centralizer ({a} : Set G)) = p := by
    rw [← Subgroup.orderOf_coe]
    exact hordc
  obtain ⟨K₀, hK₀, hPK⟩ := hemb hS _ hHK hHE p hp hp3 _ hc'ord P' hP'
  refine ⟨K₀.map (Subgroup.centralizer ({a} : Set G)).subtype, ⟨K₀, hK₀, rfl⟩, ?_⟩
  have hPK' : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤
      K₀.map (Subgroup.centralizer ({a} : Set G)).subtype := hP'eq ▸ Subgroup.map_mono hPK
  have hPL : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤ L :=
    (Subgroup.map_subtype_le _).trans inf_le_left
  refine le_antisymm ?_ (sup_le inf_le_left (Subgroup.map_subtype_le _))
  calc L = inSubgroup (aschbacherSolvableCore p) L ⊔
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := hsup.symm
    _ ≤ (L ⊓ K₀.map (Subgroup.centralizer ({a} : Set G)).subtype) ⊔
        inSubgroup (aschbacherSolvableCore p) L :=
      sup_le le_sup_right (le_sup_of_le_left (le_inf hPL hPK'))

end CFSG.RankThree.PartOne

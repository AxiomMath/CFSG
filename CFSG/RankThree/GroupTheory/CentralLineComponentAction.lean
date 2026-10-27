module

public import CFSG.RankThree.GroupTheory.CentralLineDetection
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree

open CFSG CFSG.RankThree.LocalRank

theorem center_component_le_pCore {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hθ : aschbacherSolvableCore p X = ⊥) {K : Subgroup X} (hK : IsComponent K) :
    (Subgroup.center K).map K.subtype ≤ pCore p X := by
  set E := layer X
  have hZKE : (Subgroup.center K).map K.subtype ≤ E :=
    (Subgroup.map_subtype_le _).trans (le_sSup hK)
  have hZKC : (Subgroup.center K).map K.subtype ≤ Subgroup.centralizer (E : Set X) := by
    rw [le_centralizer_layer_iff]
    intro K' hK'
    rcases LocalCores.distinct_components_commute hK hK' with rfl | hcomm
    · rintro _ ⟨z, hz, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)
    · exact (Subgroup.map_subtype_le _).trans
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have : E.Characteristic := LocalCores.layer_characteristic
  have hWn : (E ⊓ Subgroup.centralizer (E : Set X)).Normal := Subgroup.normal_inf_normal _ _
  have hWcomm : IsMulCommutative (E ⊓ Subgroup.centralizer (E : Set X) : Subgroup X) :=
    ⟨⟨fun x y => Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2.2 y y.2.1).symm⟩⟩
  have hWF : E ⊓ Subgroup.centralizer (E : Set X) ≤ fittingSubgroup X :=
    LocalCores.fitting_characteristic.2.2 _ hWn inferInstance
  exact (le_inf hZKE hZKC).trans
    (hWF.trans (fittingSubgroup_le_pCore_of_aschbacherSolvableCore_eq_bot hp hθ))

end CFSG.RankThree

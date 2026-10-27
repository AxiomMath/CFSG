module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.E2.DirectProd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

variable {H : Type*} [Group H] [Finite H]

theorem s16e_omf_generalizedFitting_eq_sup_centralizer {N : Subgroup H} [N.Normal]
    (hNlayer : N ≤ CFSG.layer H)
    (hCnil : Group.IsNilpotent ↥(Subgroup.centralizer (N : Set H))) :
    CFSG.generalizedFitting H = N ⊔ Subgroup.centralizer (N : Set H) := by
  have hlayer : CFSG.layer H = N := by
    apply le_antisymm ?_ hNlayer
    rw [CFSG.layer.eq_sSup]
    apply sSup_le
    intro K hK
    rcases CFSG.LocalCores.component_subnormal_subgroup hK
      (Subgroup.Normal.isSubnormal (inferInstance : N.Normal)) with hle | hcomm
    · exact hle
    · exfalso
      have hKC : K ≤ Subgroup.centralizer (N : Set H) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      haveI : Group.IsPerfect ↥K := hK.1.1
      haveI : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
      letI : Group.IsSolvable ↥K :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKC)
      exact Group.IsPerfect.not_isSolvable ↥K inferInstance
  have hfit : CFSG.fittingSubgroup H = Subgroup.centralizer (N : Set H) := by
    apply le_antisymm
    · have h := CFSG.LocalCores.fitting_layer_commute (G := H)
      rw [hlayer] at h
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    · exact le_sSup ⟨Subgroup.normal_centralizer, hCnil⟩
  rw [CFSG.generalizedFitting.eq_sup, hfit, hlayer, sup_comm]

theorem s16e_omf_nonempty_mulEquiv_centralizer_prod {N : Subgroup H} [N.Normal]
    (hFstar : CFSG.generalizedFitting H = N ⊔ Subgroup.centralizer (N : Set H))
    (hNdisj : N ⊓ Subgroup.centralizer (N : Set H) = ⊥) :
    Nonempty (↥(CFSG.generalizedFitting H) ≃*
      ↥(Subgroup.centralizer (N : Set H)) × ↥N) := by
  have hcomm : ∀ a ∈ Subgroup.centralizer (N : Set H), ∀ b ∈ N, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp ha b hb).symm
  have hdisj : Subgroup.centralizer (N : Set H) ⊓ N = ⊥ := by rwa [inf_comm]
  let e : ↥(Subgroup.centralizer (N : Set H)) × ↥N ≃*
      ↥(Subgroup.centralizer (N : Set H) ⊔ N) :=
    CFSG.GH74.E2.prodSupEquiv _ _ hcomm hdisj
  have hsup : N ⊔ Subgroup.centralizer (N : Set H) =
      Subgroup.centralizer (N : Set H) ⊔ N := sup_comm _ _
  rw [hFstar, hsup]
  exact ⟨e.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

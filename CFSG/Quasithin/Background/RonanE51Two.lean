module

public import CFSG.Quasithin.Background.RonanE51Basic

public section

namespace CFSG.Quasithin.RonanE51

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_twoResidual {S : Subgroup G}
    (h : Group.IsSolvable ↥(twoResidual S)) : Group.IsSolvable ↥S := by
  have hOS : twoResidual S ≤ S := twoResidual_le S
  have hNn : ((twoResidual S).subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOS).2 (le_normalizer_twoResidual S)
  have hNs : Group.IsSolvable ↥((twoResidual S).subgroupOf S) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hOS).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hOS).injective
  refine isSolvable_of_forall_pow_mem hNs fun y => ?_
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient S (y : G) y.2
  exact ⟨k, hk⟩

theorem le_pCoreOf_of_isTwoClosed {K S D : Subgroup G}
    (h2c : E1.IsTwoClosed (CFSG.solvableRadical ↥K)) (hSK : S ≤ K)
    (hSn : K ≤ Subgroup.normalizer (S : Set G)) (hD2 : IsPGroup 2 D) (hDS : D ≤ S)
    (hS : twoResidual S ≤ solvRad K) : D ≤ pCoreOf 2 K := by
  have hDK : D ≤ K := hDS.trans hSK
  have hOsolv : Group.IsSolvable ↥(twoResidual S) := by
    have := solvRad_isSolvable K
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hS)
      (Subgroup.inclusion_injective hS)
  have hSsolv : Group.IsSolvable ↥S := isSolvable_of_twoResidual hOsolv
  have hSR : S ≤ solvRad K :=
    le_solvRad hSK ((Subgroup.normal_subgroupOf_iff_le_normalizer hSK).2 hSn) hSsolv
  have hD2' : IsPGroup 2 (D.subgroupOf K) :=
    hD2.of_equiv (Subgroup.subgroupOfEquivOfLe hDK).symm
  have h1 := E3.inf_solvableRadical_eq_inf_pCore h2c hD2'
  intro d hd
  have hdR : d ∈ solvRad K := hSR (hDS hd)
  rw [solvRad_eq_map_solvableRadical] at hdR
  obtain ⟨y, hy, hyd⟩ := Subgroup.mem_map.1 hdR
  have hyD : y ∈ D.subgroupOf K := by
    rw [Subgroup.mem_subgroupOf]
    have : (y : G) = d := hyd
    rw [this]
    exact hd
  have hmem : y ∈ CFSG.solvableRadical ↥K ⊓ D.subgroupOf K := ⟨hy, hyD⟩
  rw [h1] at hmem
  exact ⟨y, hmem.1, hyd⟩

end CFSG.Quasithin.RonanE51

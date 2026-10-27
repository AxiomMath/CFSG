module

public import CFSG.Quasithin.EmptyFaithful.SBc13J1Aux
public import CFSG.Quasithin.Background.F9Comp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc13

variable {G : Type*} [Group G] [Finite G]

theorem normalizer_le_of_normal_of_not_le {X N J : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hJ : J ∈ cComp X) (hJN : ¬ J ≤ N) :
    N ≤ Subgroup.normalizer (J : Set G) := by
  rcases cComp_commutator_dichotomy_of_le hJ hNX with ⟨-, hsolv⟩ | hconj
  · exact le_normalizer_of_commutator_solvable_J1 hNX hJ hsolv
  · exfalso
    apply hJN
    calc J ≤ conjClosure J N := le_conjClosure J N
      _ = ⁅J, N⁆ := hconj.symm
      _ ≤ N := Subgroup.le_normalizer_iff_commutator_le_right.mp
        ((le_of_mem_cComp hJ).trans hXN)

theorem commutator_eq_of_not_le_pCore {J K : Subgroup G} (hJp : ⁅J, J⁆ = J)
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hK : K ≤ Subgroup.normalizer (J : Set G))
    (h : ¬ ⁅J, K⁆ ≤ pCoreOf 2 J) : ⁅J, K⁆ = J := by
  have hDJ : ⁅J, K⁆ ≤ J := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hK
  have hDn : (⁅J, K⁆.subgroupOf J).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (A3.le_normalizer_commutator_left J K)
  rcases sup_pCoreOf_eq_or_commutator_le_J1 hJq hDJ hDn with hsup | hcomm
  · have h1 := perfectCore_le_of_sup_solvable hDJ hDn hsup.symm (isSolvable_pCoreOf_J1 J)
    rw [perfectCore_eq_self_of_perfect hJp] at h1
    exact le_antisymm hDJ h1
  · exfalso
    apply h
    have hQJ : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) := le_normalizer_pCoreOf 2 J
    have hQK : K ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
      hK.trans (normalizer_le_normalizer_pCoreOf 2 J)
    have h1 := commutator_le_of_commutator_commutator_le hQK hQJ hJp hcomm
    rwa [Subgroup.commutator_comm] at h1

theorem commutator_le_pCore_of_normal {X N J : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hJ : J ∈ cComp X)
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hJN : ¬ J ≤ N) :
    ⁅J, N⁆ ≤ pCoreOf 2 J := by
  by_contra h
  have hNJ := normalizer_le_of_normal_of_not_le hNX hXN hJ hJN
  have hJeq := commutator_eq_of_not_le_pCore (perfect_of_mem_cComp hJ) hJq hNJ h
  exact hJN (hJeq.symm.le.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp
    ((le_of_mem_cComp hJ).trans hXN)))

theorem pCoreOf_le_pCoreOf_of_subnormal {X J : Subgroup G} (hJ : J ∈ cComp X) :
    pCoreOf 2 J ≤ pCoreOf 2 X :=
  pCoreOf_le_pCoreOf_of_isSubnormal (subnormal_of_mem_cComp hJ)

end SBc13

end CFSG.Quasithin

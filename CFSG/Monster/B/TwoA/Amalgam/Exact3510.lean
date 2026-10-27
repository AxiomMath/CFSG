module

public import CFSG.Monster.B.TwoA.Amalgam.Exact3510Core
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeType
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

theorem native_order_three_common_neighbors_exact_3510 :
    (∀ v w : CVert, w ∈ sphereThree v →
      (cgraph.induce (cgraph.commonNeighbors v w)).Connected ∧
      (∀ [Fintype (cgraph.commonNeighbors v w)]
        [DecidableRel (cgraph.induce (cgraph.commonNeighbors v w)).Adj],
        (cgraph.induce (cgraph.commonNeighbors v w)).IsSRGWith 3510 693 180 126) ∧
      (cgraph.commonNeighbors v w).ncard = 3510 ∧
      (sphereThree v).ncard = 2370830336 ∧
      (∀ s ∈ vStab v ⊓ vStab w, (∀ x ∈ cgraph.commonNeighbors v w, cvMul x s = x) → s = 1) ∧
      Nat.card (vStab v ⊓ vStab w : Subgroup Shat) = 129123503308800) ∧
    ∀ μ₃ : ℕ, (∀ v w : CVert, w ∈ sphereThree v → (cgraph.commonNeighbors v w).ncard = μ₃) →
      μ₃ = 3510 := by
  have hType : ∀ ⦃v w u z : CVert⦄, w ∈ sphereThree v → u ∈ cgraph.commonNeighbors v w →
      z ∈ cgraph.commonNeighbors v w → u ≠ z → ¬cgraph.Adj u z → z ∈ sphereThree u :=
    fun _ _ _ _ hw hu hz huz hna => mem_sphereThree_of_mem_commonNeighbors hw hu hz huz hna
  refine ⟨fun v w hw => ⟨cn_connected hType hw, fun {_ _} => cn_isSRGWith hType hw,
    ncard_commonNeighbors_eq_3510 hType hw, ncard_sphereThree_eq hType v,
    (native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw).2.2.1,
    natCard_pairStab_eq hType hw⟩, fun μ₃ hμ => ?_⟩
  obtain ⟨w, hw⟩ := sphereThree_nonempty exists_rootModel cv0
  rw [← hμ cv0 w hw, ncard_commonNeighbors_eq_3510 hType hw]

end CFSG.Monster.B.TwoA.Amalgam

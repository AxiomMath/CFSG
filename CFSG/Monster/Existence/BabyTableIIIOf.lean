module

public import CFSG.Monster.Existence.BabyW2Classes
public import CFSG.Monster.Existence.TwoPoint.ShapeOneHC
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
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
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
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.GMS CFSG.Blueprint MulOpposite

@[expose] noncomputable def babyRep
    (i : ℕ) : NativeSporadic.B := CTIB.iotaEquiv.symm (CTIB.rs i)

@[expose] def babyRepClass (i : ℕ) : Fin 4 :=
  if i = 1 then 0 else if i = 0 then 1 else if i = 3 then 2 else 3

theorem babyTableIII_of_reps
    (h : ∀ i ∈ [1, 0, 5, 3], Nat.card ↥(Subgroup.centralizer ({babyRep i} : Set NativeSporadic.B)) =
      babyCentOrder (babyRepClass i)) :
    BabyTableIII := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, -⟩ := CTIB.native_four_involution_classes
  have hcls : ∀ t : NativeSporadic.B, orderOf t = 2 →
      ∃ i ∈ [1, 0, 5, 3], IsConj t (babyRep i) ∧ BabyInv (babyRepClass i) t := by
    intro t ht
    obtain ⟨i, ⟨hi, hc⟩, -⟩ := hB t ht
    exact ⟨i, hi, hc, ht, (natCard_centralizer_eq_of_isConj hc).trans (h i hi)⟩
  refine ⟨fun t ht => ?_, fun k s t hs ht => ?_⟩
  · obtain ⟨i, -, -, hk⟩ := hcls t ht
    exact ⟨_, hk⟩
  · obtain ⟨i, hi, hsi, hki⟩ := hcls s hs.1
    obtain ⟨j, hj, htj, hkj⟩ := hcls t ht.1
    have e1 := BabyInv.unique hki hs
    have e2 := BabyInv.unique hkj ht
    have hij : i = j := by
      have : babyRepClass i = babyRepClass j := e1.trans e2.symm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;>
        first | rfl | (exfalso; revert this; decide)
    subst hij
    exact hsi.trans htj.symm

theorem natCard_centralizer_rep_zero :
    Nat.card ↥(Subgroup.centralizer ({babyRep 0} : Set NativeSporadic.B)) = babyCentOrder 1 :=
  (natCard_centralizer_eq_of_isConj
    (isConj_rep_zero_of_rank orderOf_phiB_xBar rank_phiB_xBar_sub_one).symm).trans
    natCard_centralizer_babyW2

theorem orderOf_phiB_uBar :
    orderOf (phiB uBar) = 2 :=
  (@MulEquiv.orderOf_eq _ _ _ Units.instMonoid phiB uBar).trans orderOf_uBar

theorem isConj_rep_one_of_rank
    {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 1860) : IsConj X (babyRep 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, -, b1, b0, b5, b3⟩ := CTIB.native_four_involution_classes
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := hB X hX
  have hrk := rank_sub_one_of_isConj hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact hc
  · rw [hr, b0] at hrk
    exact absurd hrk (by norm_num)
  · rw [hr, b5] at hrk
    exact absurd hrk (by norm_num)
  · rw [hr, b3] at hrk
    exact absurd hrk (by norm_num)

theorem natCard_centralizer_rep_one_of
    (hC : CTIB.CentralizerInput) :
    Nat.card ↥(Subgroup.centralizer ({babyRep 1} : Set NativeSporadic.B)) = babyCentOrder 0 := by
  rw [← natCard_centralizer_eq_of_isConj
    (isConj_rep_one_of_rank orderOf_phiB_uBar rank_phiB_uBar_sub_one)]
  have h1 := Nat.card_congr
    (@centralizerMulEquiv Cbar NativeSporadic.B _ Units.instGroup phiB uBar).toEquiv
  obtain ⟨Ψ⟩ := CTIB.centralizer_equiv_Eam hC
    (CTIB.isConj_labelS_of_rank orderOf_op_uBar rank_betaS_op_uBar)
  rw [← h1, ← Nat.card_congr centOpUBarEquiv.toEquiv, Nat.card_congr Ψ.toEquiv, natCard_Eam,
    CFSG.LieType.Chevalley.C2E6Std.card_stdGroup]
  norm_num [babyCentOrder]

theorem babyTableIII_of
    (hC : CTIB.CentralizerInput)
    (h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) = babyCentOrder 2)
    (h5 : Nat.card ↥(Subgroup.centralizer ({babyRep 5} : Set NativeSporadic.B)) = babyCentOrder 3) :
    BabyTableIII := by
  refine babyTableIII_of_reps fun i hi => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact natCard_centralizer_rep_one_of hC
  · exact natCard_centralizer_rep_zero
  · exact h5
  · exact h3

end CFSG.Monster.Existence

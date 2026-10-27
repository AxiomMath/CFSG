module

public import CFSG.Open.SporadicBabyMonsterRecognitionMilestoneDefs
public import CFSG.Monster.Existence.BabyOrder
public import CFSG.Sporadic.B
public import CFSG.Monster.B.GSide.CompletionFusion
public import CFSG.Monster.B.GSide.HInnerFusion
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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate3011
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
public import Certificates.Certificate3059
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
public import Certificates.Certificate3080
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3175
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16026
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate16042
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.CTIB

@[expose] def labelB :
    NativeSporadic.B := iotaEquiv.symm labelS

theorem orderOf_labelS :
    orderOf labelS = 2 := by
  have h : orderOf (sEquiv labelS) = orderOf labelS := MulEquiv.orderOf_eq sEquiv _
  rw [sEquiv_labelS_eq_cV0, orderOf_coe_cV0] at h
  exact h.symm

theorem orderOf_labelB :
    orderOf labelB = 2 := by
  have h : orderOf (iotaEquiv.symm labelS) = orderOf labelS := by
    with_reducible_and_instances exact MulEquiv.orderOf_eq iotaEquiv.symm _
  exact h.trans orderOf_labelS

theorem rank_labelB :
    Matrix.rank (labelB.val.val - 1) = 1860 :=
  (rank_iotaEquiv_symm labelS).trans rank_labelS

theorem natCard_centralizer_labelS :
    Nat.card (Subgroup.centralizer {labelS}) = 306129918735099415756800 := by
  have h := Nat.card_congr (centralizerEquiv sEquiv labelS).toEquiv
  rw [sEquiv_labelS_eq_cV0, natCard_centralizer_cV0] at h
  exact h

theorem natCard_centralizer_labelB :
    Nat.card (Subgroup.centralizer ({labelB} : Set NativeSporadic.B)) =
      4 * CFSG.Open.sporadicOrderTwistedE6Two := by
  have e : Subgroup.centralizer {labelS} ≃*
      Subgroup.centralizer ({iotaEquiv.symm labelS} : Set NativeSporadic.B) := by
    with_reducible_and_instances exact centralizerEquiv iotaEquiv.symm labelS
  have h := (Nat.card_congr e.toEquiv).symm.trans natCard_centralizer_labelS
  exact h.trans (by norm_num [CFSG.Open.sporadicOrderTwistedE6Two])

theorem recognition_exists_of_models
    (hmodels : ∀ (d₀ : NativeSporadic.B) (_ : orderOf d₀ = 2)
      (_ : Matrix.rank (d₀.val.val - 1) = 1860)
      (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
      (d : G) (_ : orderOf d = 2)
      (_ : Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
        Subgroup.centralizer ({d₀} : Set NativeSporadic.B))),
      Nonempty (G ≃* NativeSporadic.B)) :
    ∃ (B : Type) (_ : Group B) (_ : Finite B), IsSimpleGroup B ∧
      Nat.card B = CFSG.Open.sporadicOrderBabyMonster ∧
      ∃ d₀ : B, orderOf d₀ = 2 ∧
        Nat.card (Subgroup.centralizer ({d₀} : Set B)) =
          4 * CFSG.Open.sporadicOrderTwistedE6Two ∧
        ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
          ∀ d : G, orderOf d = 2 →
            Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
              Subgroup.centralizer ({d₀} : Set B)) →
            Nonempty (G ≃* B) :=
  ⟨NativeSporadic.B, inferInstance, inferInstance, CFSG.Sporadic.B.fam_b_simplicity,
    CFSG.Monster.Existence.card_nativeB, labelB, orderOf_labelB, natCard_centralizer_labelB,
    fun G _ _ hG d hd hc => @hmodels labelB orderOf_labelB rank_labelB G _ _ hG d hd hc⟩

end CFSG.Monster.B.GSide

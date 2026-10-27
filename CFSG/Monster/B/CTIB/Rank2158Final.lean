module

public import CFSG.Monster.B.CTIB.Rank2158
public import CFSG.Monster.B.CTIB.DistThreeProductCent
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootNative
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
public import Certificates.Certificate3121
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
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

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem commutator_self_le {G : Type*} [Group G] (R : Subgroup G) : ⁅R, R⁆ ≤ R :=
  Subgroup.commutator_le.2 fun _ hg _ hh =>
    R.mul_mem (R.mul_mem (R.mul_mem hg hh) (R.inv_mem hg)) (R.inv_mem hh)

theorem distThreeProduct_of_pair
    {v w : CVert} (hvw : cgraph.dist v w = 3)
    {R F C : Subgroup Shat} (hR : R = Subgroup.centralizer {clabelS v, clabelS w})
    (hF : F = ⁅R, R⁆) (hC : C = Subgroup.centralizer {clabelS v * clabelS w}) :
    ∃ F' : Subgroup C, CFSG.IsComponent F' ∧ (∀ K : Subgroup C, CFSG.IsComponent K → K = F') ∧
      IsSimpleGroup F' ∧ Nonempty (F' ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
      Nat.card F' = 3311126603366400 := by
  have hL := labelsInput_of_ambient ambientRootOrbitsHyp
  have hO := outerInput_of_ambient ambientRootOrbitsHyp
  have hP := pathInput_of_ambient ambientRootOrbitsHyp
  have hT := typeThreeBoundInput_of_ambient ambientRootOrbitsHyp
  obtain ⟨-, -, hRC, -, -, -, -, -, hFcard, hcomp, huniq, -, hFsimple, -, ⟨Ψ, -, hiso⟩, -⟩ :=
    distance_three_product_full_centralizer hL hO hP hT hvw hR hF hC
  have hsv : clabelS w ∈ vStab v := (hL v w hvw).1
  obtain ⟨ρ, iv, hρ, hρs⟩ := exists_compat_beta hO hP hT hvw ⟨clabelS w, hsv⟩ rfl
  obtain ⟨φ, -, e, -⟩ := hiso ρ hρ.1 hρ.2.1 ⟨clabelS w, hsv⟩ rfl hρs
  have hFC : F ≤ C := hF ▸ (commutator_self_le R).trans hRC
  refine ⟨F.subgroupOf C, hcomp, huniq,
    @MulEquiv.isSimpleGroup _ _ _ _ hFsimple (Subgroup.subgroupOfEquivOfLe hFC),
    ⟨(Subgroup.subgroupOfEquivOfLe hFC).trans e⟩, ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv, hFcard]

theorem distThreeProductInput_holds :
    DistThreeProductInput :=
  fun _ _ hvw => distThreeProduct_of_pair hvw rfl rfl rfl

theorem native_rank_2158_distance_three_product_final :
    (∃ v u : CVert, cgraph.dist v u = 3 ∧ IsConj (sEquiv (rs 5)) (clabelS v * clabelS u)) ∧
    (∀ s : Sbp, orderOf s = 2 → ((βr s) - 1).rank = 2158 →
      ∃ K : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K ∧
        (∀ K' : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K' → K' = K) ∧
        IsSimpleGroup K ∧ Nonempty (K ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
        Nat.card K = 3311126603366400 ∧ 17 ∣ Nat.card K) ∧
    ∀ X : NativeSporadic.B, orderOf X = 2 → (X.val.val - 1).rank = 2158 →
      ∃ K : Subgroup (Subgroup.centralizer {X}), CFSG.IsComponent K ∧
        (∀ K' : Subgroup (Subgroup.centralizer {X}), CFSG.IsComponent K' → K' = K) ∧
        IsSimpleGroup K ∧ Nonempty (K ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
        Nat.card K = 3311126603366400 ∧ 17 ∣ Nat.card K :=
  native_rank_2158_distance_three_product_of ambientRootOrbitsHyp distThreeProductInput_holds

end CFSG.Monster.B.CTIB

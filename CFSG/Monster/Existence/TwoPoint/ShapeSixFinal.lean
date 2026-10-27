module

public import CFSG.Monster.Existence.TwoPoint.ShapeSixAssembly
public import CFSG.Monster.B.CTIB.Rank2158Final
public import CFSG.Monster.B.CTIB.DistThreeProductFinal
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
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3023
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
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6006
public import Certificates.Certificate6007
public import Certificates.Certificate6009
public import Certificates.Certificate6010
public import Certificates.Certificate6011
public import Certificates.Certificate6012
public import Certificates.Certificate6013
public import Certificates.Certificate6014
public import Certificates.Certificate6015
public import Certificates.Certificate6016
public import Certificates.Certificate6017
public import Certificates.Certificate6018
public import Certificates.Certificate6021
public import Certificates.Certificate6022
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16018
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
public import Certificates.Certificate3024
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate8955
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

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.GMS CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam
open scoped commutatorElement

theorem exists_conj_clabelS
    (v : CVert) :
    ∃ g : Shat, ((clabelS v : Shat) : Dfull) = (g : Dfull)⁻¹ * cQ * g := by
  obtain ⟨g, rfl⟩ := cvOf_surjective v
  exact ⟨g, by rw [coe_clabelS, clabel_cvOf]⟩

theorem exists_shapeSix_MGriess
    (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hT3 : BabyTableIII) {b z u : MGriess} (hV : TableV tGriess b z u) :
    ∃ y, y ∈ tableVIISet tGriess xGriess tGriess .four_B ∧
      TwoPointShape (cent2 tGriess y) 6 := by
  obtain ⟨⟨v, w, hvw, -⟩, -⟩ := CTIB.native_rank_2158_distance_three_product_final
  obtain ⟨-, -, hne, hcomm⟩ := labelsInput_of_ambient ambientRootOrbitsHyp v w hvw
  obtain ⟨-, -, hRC, hrel, -, hCcard, -, -, hFcard, hcomp, -⟩ :=
    CTIB.distance_three_product_full_centralizer_final hvw
      (R := Subgroup.centralizer {clabelS v, clabelS w})
      (F := ⁅Subgroup.centralizer {clabelS v, clabelS w},
        Subgroup.centralizer {clabelS v, clabelS w}⁆)
      (C := Subgroup.centralizer {clabelS v * clabelS w}) rfl rfl rfl
  obtain ⟨F', hF'comp, hF'uniq, -, hF'ad, -⟩ := CTIB.distThreeProduct_of_pair hvw
    (R := Subgroup.centralizer {clabelS v, clabelS w})
    (F := ⁅Subgroup.centralizer {clabelS v, clabelS w},
      Subgroup.centralizer {clabelS v, clabelS w}⁆)
    (C := Subgroup.centralizer {clabelS v * clabelS w}) rfl rfl rfl
  exact exists_shapeSix_of_product_data hcard hT3 hV (exists_conj_clabelS v)
    (exists_conj_clabelS w) hcomm.symm.eq hne.symm rfl rfl rfl hRC hrel hCcard hFcard hcomp
    ⟨F', hF'comp, hF'uniq, hF'ad⟩

end CFSG.Monster.Existence

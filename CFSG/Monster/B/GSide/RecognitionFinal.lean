module

public import CFSG.Monster.B.GSide.RecognitionBT2
public import CFSG.Monster.B.GSide.BT2Bridge
public import CFSG.Monster.B.GSide.HSylowBeta
public import CFSG.Monster.B.GSide.HInnerFusionY3
public import CFSG.Monster.B.GSide.EdgeQCertDC
public import CFSG.Monster.B.GSide.EdgeQCertWit
public import CFSG.Monster.B.GSide.TwoDCentralizer
public import CFSG.Monster.B.TwoA.Amalgam.NativeChain
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
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3013
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
public import Certificates.Certificate3024
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3043
public import Certificates.Certificate3044
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
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3130
public import Certificates.Certificate3131
public import Certificates.Certificate3132
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3137
public import Certificates.Certificate3175
public import Certificates.Certificate3176
public import Certificates.Certificate3178
public import Certificates.Certificate3179
public import Certificates.Certificate6007
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate16001
public import Certificates.Certificate16005
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
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate16042
public import Certificates.Certificate3135
public import Certificates.Certificate3136
public import Certificates.Certificate16951
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate3951
public import Certificates.Certificate8955
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

theorem exists_mem_FA :
    ∃ β : vStab cv0, β ∈ FA := by
  obtain ⟨u, hu⟩ := sphereDistThree_nonempty_of_ambient ambientRootOrbitsHyp cv0
  exact ⟨⟨clabelS u, clabelS_mem_vStab_cv0_of_dist_three hu⟩, u, hu, rfl⟩

theorem hc5ii_of_extremal
    {X : Subgroup (vStab cv0)}
    (h6 : ∀ u ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆, u = 1 ∨ cV0 * u ∈ RA ∨
      (u * u = 1 ∧ u ∈ commutator (vStab cv0) ∧ u ∉ RA ∧ u ∉ RB ∧ u ≠ cV0 ∧
        rkH u = 2048 ∧ rkH (cV0 * u) = 2168)) :
    ∀ u ∈ centerInfCommutator X, u ≠ 1 →
      cV0 * u ∈ RA ∨ (u * u = 1 ∧ rkH u = 2048 ∧ rkH (cV0 * u) ≠ 1860) := by
  intro u hu hu1
  rcases (h6 u hu).resolve_left hu1 with h | ⟨h2, -, -, -, -, hr, hr'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h2, hr, by rw [hr']; decide⟩

theorem gamma2D_of_gold
    (hGold : GoldschmidtTheorem) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] {d : G}, d ≠ 1 →
      ∀ (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G),
      (∀ a : vStab cv0, Φ a = psiInvHom ψ a) →
      conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d →
      (∀ s : Shat, orderOf s = 2 → rankS s = 2048 → Subgroup.centralizer {Φ s} ≤ Φ.range) →
      ∀ s : Shat, orderOf s = 2 → rankS s = 2168 → Subgroup.centralizer {Φ s} ≤ Φ.range := by
  intro G _ _ _ d hd1 ψ Φ hΦ hDM _ s hs hrk
  exact centralizer_le_range_of_rankS_eq_2168_of_gold hd1 ψ Φ hΦ hDM hGold hs hrk

theorem recognition_models_of_gold
    (hGold : GoldschmidtTheorem)
    (d₀ : NativeSporadic.B) (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (d : G) (hd : orderOf d = 2)
    (hcentralizer : Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
      Subgroup.centralizer ({d₀} : Set NativeSporadic.B))) :
    Nonempty (G ≃* NativeSporadic.B) := by
  obtain ⟨β, hβ⟩ := exists_mem_FA
  obtain ⟨X, hXβ, hX⟩ := exists_sylow_centralizer_beta hβ
  obtain ⟨hβ2, hβK, ⟨T, hXT⟩, hcX, hβX, hXsyl, hZ, hcU, hβcU, hHC5, h6⟩ :=
    native_HC5_extremal_data hβ hXβ hX
  exact recognition_of_inputs bt2C1 T hβ2 hβK hXT hcX hβX hXβ hXsyl hX hZ hcU hβcU hHC5
    (hc5ii_of_extremal h6) hY3_native_all edgeQ_unique_center edgeQCert_hWit hGold
    (gamma2D_of_gold hGold) d₀ hd₀ hrank G d hd hcentralizer

end CFSG.Monster.B.GSide

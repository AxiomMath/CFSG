module

public import CFSG.Monster.B.CTIB.UniqueComponentFinal
public import CFSG.Monster.B.CTIB.Rank2048
public import CFSG.Monster.B.CTIB.Rank2168Final
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
public import Certificates.Certificate3176
public import Certificates.Certificate6007
public import Certificates.Certificate6023
public import Certificates.Certificate6024
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
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Monster.B CFSG.LieType.Chevalley.C2E6Std
open CFSG.Sporadic.Co2Inv (co2_involution_input)

theorem quotientCenter_map_equiv {G H : Type*} [Group G] [Group H] (Ψ : G ≃* H)
    (K : Subgroup G) :
    Nonempty (K ⧸ Subgroup.center K ≃*
      K.map Ψ.toMonoidHom ⧸ Subgroup.center (K.map Ψ.toMonoidHom)) :=
  ⟨QuotientGroup.congr _ _ (K.equivMapOfInjective Ψ.toMonoidHom Ψ.injective)
    (Subgroup.map_center_eq (K.equivMapOfInjective Ψ.toMonoidHom Ψ.injective))⟩

theorem center_eq_bot_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (hq : CFSG.IsQuasisimple G) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hx : x ∈ Subgroup.center G := h ▸ Subgroup.mem_top x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hx y]

theorem involution_local_components_simple_quotient_divisible_by_seventeen
    {T : Type*}
    [Group T] (hT : Nonempty (T ≃* NativeSporadic.B)) :
    ∀ t : T, orderOf t = 2 → ∀ K : Subgroup (Subgroup.centralizer {t}), CFSG.IsComponent K →
      IsSimpleGroup (K ⧸ Subgroup.center K) ∧
      (Nonempty (K ⧸ Subgroup.center K ≃* stdGroup) ∨
        Nonempty (K ⧸ Subgroup.center K ≃* adjointGroup Tag.F4 (ZMod 2))) ∧
      17 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  intro t ht K hK
  obtain ⟨e⟩ := hT
  have hs : orderOf ((e.trans iotaEquiv) t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  have hK' := CFSG.LocalCores.isComponent_map_mulEquiv (centralizerEquiv (e.trans iotaEquiv) t) hK
  obtain ⟨eQ⟩ := quotientCenter_map_equiv (centralizerEquiv (e.trans iotaEquiv) t) K
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := four_classes co2_involution_input hs
  have hr := rank_beta_conj hc
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  refine ⟨hK.1.2.1, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · rw [h1] at hr
    obtain ⟨K₀, -, hU, -, -, ⟨θ⟩, -, h17⟩ := native_rank_1860_unique_component_final _ hs hr
    obtain rfl := hU _ hK'
    refine ⟨Or.inl ⟨eQ.trans θ⟩, ?_⟩
    rw [Nat.card_congr eQ.toEquiv]
    exact h17
  · rw [h0] at hr
    exact absurd hK' ((native_rank_2048_centralizer_has_no_components _ hs hr).elim
      fun _ hc => hc.2.2.2.elim fun _ hQ => hQ.2.2.2.2.2.2.2 _)
  · rw [h5] at hr
    obtain ⟨K₀, hK₀, hU, hS, ⟨θ⟩, -, h17⟩ :=
      native_rank_2158_distance_three_product_final.2.1 _ hs hr
    obtain rfl := hU _ hK'
    have hbot := @center_eq_bot_of_isSimpleGroup _ _ hS hK₀.1
    have e₀ := (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    refine ⟨Or.inr ⟨(eQ.trans e₀).trans θ⟩, ?_⟩
    rw [Nat.card_congr (eQ.trans e₀).toEquiv]
    exact h17
  · rw [h3] at hr
    exact absurd hK' ((native_rank_2168_centralizer_has_no_components _ hs hr).2.2 _)

end CFSG.Monster.B.CTIB

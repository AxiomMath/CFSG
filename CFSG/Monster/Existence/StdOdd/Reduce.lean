module

public import CFSG.Monster.Existence.StdOdd.Defs
public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.Existence.BabyW3Classes
public import CFSG.Monster.B.TwoA.Amalgam.DerivedCoverMain
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
public import Certificates.Certificate3024
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
public import Certificates.Certificate6020
public import Certificates.Certificate6021
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate6026
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate10072
public import Certificates.Certificate10073
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16018
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16030
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

namespace CFSG.Monster.Existence.StdOdd

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.GMS CFSG.Blueprint
  CFSG.LieType.Chevalley.C2E6Std

private theorem eq_one_of_pow_eq_one_of_odd {X : Type*} [Group X] {x : X} {n : ℕ} (hn : Odd n)
    (h1 : x ^ n = 1) (h2 : x ^ 2 = 1) : x = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rwa [pow_succ, pow_mul, h2, one_pow, one_mul] at h1

theorem injective_of_odd_of_sq_eq_one {M K : Type*} [Group M] [Group K]
    (hM : Odd (Nat.card M)) (g : M →* K) (h : ∀ m : M, g m = 1 → m ^ 2 = 1) :
    Function.Injective g := by
  rw [injective_iff_map_eq_one]
  exact fun m hm => eq_one_of_pow_eq_one_of_odd hM pow_card_eq_one' (h m hm)

theorem map_mem_of_index_eq_two {M G : Type*} [Group M] [Group G] {K : Subgroup G}
    (hK : K.index = 2) (hM : Odd (Nat.card M)) (f : M →* G) (m : M) : f m ∈ K := by
  have := Subgroup.normal_of_index_eq_two hK
  set g : M →* G ⧸ K := (QuotientGroup.mk' K).comp f with hg
  have h2 : g m ^ 2 = 1 := by
    have := pow_card_eq_one' (G := G ⧸ K) (x := g m)
    rwa [show Nat.card (G ⧸ K) = 2 from hK] at this
  have h1 : g m ^ Nat.card M = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  exact (QuotientGroup.eq_one_iff _).1 (eq_one_of_pow_eq_one_of_odd hM h1 h2)

theorem exists_injective_of_index_two_of_card_two {E T M : Type*} [Group E] [Group T] [Group M]
    {K Z : Subgroup E} [Z.Normal] (hK : K.index = 2) (hZ : Nat.card Z = 2)
    (e : K ⧸ Z.subgroupOf K ≃* T) (hM : Odd (Nat.card M)) (f : M →* E)
    (hf : Function.Injective f) : ∃ g : M →* T, Function.Injective g := by
  have hmem : ∀ m : M, f m ∈ K := map_mem_of_index_eq_two hK hM f
  set f' : M →* K := f.codRestrict K hmem with hf'
  set g : M →* T := (e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf K))).comp f' with hg
  refine ⟨g, injective_of_odd_of_sq_eq_one hM g fun m hm => ?_⟩
  have h1 : f' m ∈ Z.subgroupOf K := by
    rw [← QuotientGroup.eq_one_iff]
    exact (MulEquiv.map_eq_one_iff e).1 hm
  have h2 : f m ∈ Z := Subgroup.mem_subgroupOf.1 h1
  have h3 : f m ^ 2 = 1 := by
    have := pow_card_eq_one' (x := (⟨f m, h2⟩ : Z))
    rw [hZ] at this
    exact congrArg Subtype.val this
  exact hf (by rw [map_pow, h3, map_one])

theorem exists_injective_stdGroup_of_injective_Eam
    {M : Type*} [Group M]
    (hM : Odd (Nat.card M)) (f : M →* ↥Eam) (hf : Function.Injective f) :
    ∃ g : M →* ↥stdGroup, Function.Injective g := by
  obtain ⟨hidx, -, -, -, hZ2, ⟨e⟩, -⟩ := short_F4_derived_standard_perfect_cover
  exact exists_injective_of_index_two_of_card_two hidx hZ2 e hM f hf

private theorem nonempty_centralizer_mulEquiv_of_isConj {G : Type*} [Group G] {a b : G}
    (h : IsConj a b) :
    Nonempty (↥(Subgroup.centralizer ({a} : Set G)) ≃* ↥(Subgroup.centralizer ({b} : Set G))) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have e := centralizerMulEquiv (MulAut.conj c) a
  rw [MulAut.conj_apply, hc] at e
  exact ⟨e⟩

private theorem exists_injective_of_le_centralizer {G H : Type*} [Group G] [Group H] {a : G}
    {M : Subgroup G} (hM : M ≤ Subgroup.centralizer ({a} : Set G))
    (e : ↥(Subgroup.centralizer ({a} : Set G)) ≃* H) :
    ∃ f : ↥M →* H, Function.Injective f :=
  ⟨(e : _ →* _).comp (Subgroup.inclusion hM), e.injective.comp (Subgroup.inclusion_injective hM)⟩

theorem nonempty_centralizer_phiB_uBar_mulEquiv_Eam
    (hC : CTIB.CentralizerInput) :
    Nonempty (↥(Subgroup.centralizer ({phiB uBar} : Set NativeSporadic.B)) ≃* ↥Eam) := by
  obtain ⟨Ψ⟩ := CTIB.centralizer_equiv_Eam hC
    (CTIB.isConj_labelS_of_rank orderOf_op_uBar rank_betaS_op_uBar)
  exact ⟨((@centralizerMulEquiv Cbar NativeSporadic.B _ Units.instGroup phiB uBar).symm.trans
    centOpUBarEquiv.symm).trans Ψ⟩

theorem nonempty_centralizer_mulEquiv_Eam_of_babyInv_zero
    (h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) ≠ babyCentOrder 0)
    {r : NativeSporadic.B} (hr : BabyInv 0 r) :
    Nonempty (↥(Subgroup.centralizer ({r} : Set NativeSporadic.B)) ≃* ↥Eam) := by
  have hconj : IsConj r (phiB uBar) := (isConj_babyRep_one_of_babyInv_zero h3 hr).trans
    (isConj_rep_one_of_rank orderOf_phiB_uBar rank_phiB_uBar_sub_one).symm
  obtain ⟨e₁⟩ := nonempty_centralizer_mulEquiv_of_isConj hconj
  obtain ⟨e₂⟩ := nonempty_centralizer_phiB_uBar_mulEquiv_Eam centralizerInput_B
  exact ⟨e₁.trans e₂⟩

theorem exists_subgroup_stdGroup_card_eq
    (h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) ≠ babyCentOrder 0)
    {r : NativeSporadic.B} (hr : BabyInv 0 r) {M : Subgroup NativeSporadic.B}
    (hM : M ≤ Subgroup.centralizer ({r} : Set NativeSporadic.B)) (hodd : Odd (Nat.card M)) :
    ∃ N : Subgroup Rgrp, Nat.card N = Nat.card M := by
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_Eam_of_babyInv_zero h3 hr
  obtain ⟨f, hf⟩ := exists_injective_of_le_centralizer hM e
  obtain ⟨g, hg⟩ := exists_injective_stdGroup_of_injective_Eam hodd f hf
  exact ⟨g.range, Nat.card_congr (MonoidHom.ofInjective hg).toEquiv.symm⟩

end CFSG.Monster.Existence.StdOdd

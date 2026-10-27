module

public import CFSG.Monster.B.GSide.HInnerFusionI3Cert
public import CFSG.Monster.B.GSide.HInnerFusionDefs
public import CFSG.Monster.B.GSide.G4TwoC
public import CFSG.Monster.B.CTIB.DistThreeProductCore
public import CFSG.Monster.B.CTIB.SylowCenter
public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.Monster.B.TwoA.Amalgam.NativeChain
public import CFSG.Monster.B.TwoA.Amalgam.GlobalTypeRemain
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
public import Certificates.Certificate3013
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
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3135
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

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam ConjAct
open CFSG.Monster.B.CTIB.Native (qmul gArr liftImgsN sqCode autApply qinv fuse wordAut
  genInvImgs centWordN deltaN countBelow natCertOK natBfs fusionRecsN)
open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem natCard_inf_centralizer_mul_ncard {G : Type*} [Group G] [Finite G] (K : Subgroup G)
    {t : G} (ht : t ∈ K) :
    Nat.card ↥(K ⊓ Subgroup.centralizer {t}) * {u | ∃ k ∈ K, u = k * t * k⁻¹}.ncard =
      Nat.card K := by
  set r : K := ⟨t, ht⟩ with hr
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct K) r)
  rw [MulAction.index_stabilizer, ← Subgroup.nat_card_centralizer_nat_card_stabilizer] at h1
  have horb : (MulAction.orbit (ConjAct K) r).ncard = {u | ∃ k ∈ K, u = k * t * k⁻¹}.ncard := by
    have e : Subtype.val '' MulAction.orbit (ConjAct K) r = {u | ∃ k ∈ K, u = k * t * k⁻¹} := by
      ext u
      simp only [Set.mem_image, ConjAct.mem_orbit_conjAct, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨c, hc⟩ := isConj_iff.1 hy.symm
        exact ⟨c, c.2, by rw [← hc]; rfl⟩
      · rintro ⟨k, hk, rfl⟩
        have hm : k * t * k⁻¹ ∈ K := K.mul_mem (K.mul_mem hk ht) (K.inv_mem hk)
        have hc : IsConj r ⟨k * t * k⁻¹, hm⟩ := isConj_iff.2 ⟨⟨k, hk⟩, Subtype.ext rfl⟩
        exact ⟨⟨k * t * k⁻¹, hm⟩, hc.symm, rfl⟩
    rw [← e, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hcent : Nat.card (Subgroup.centralizer ({r} : Set K)) =
      Nat.card ↥(K ⊓ Subgroup.centralizer {t}) := by
    have e : (Subgroup.centralizer ({r} : Set K)).map K.subtype =
        K ⊓ Subgroup.centralizer {t} := by
      ext u
      simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, ?_⟩
        have := congrArg Subtype.val hy
        simpa [hr] using this
      · rintro ⟨hu, h⟩
        exact ⟨⟨u, hu⟩, Subtype.ext (by simpa [hr] using h), rfl⟩
    rw [← e, Subgroup.card_map_of_injective K.subtype_injective]
  rw [hcent, horb, Nat.card_congr ConjAct.toConjAct.symm.toEquiv] at h1
  exact h1

theorem natCard_centralizer_conj {G : Type*} [Group G] (g u : G) :
    Nat.card (Subgroup.centralizer ({g * u * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({u} : Set G)) := by
  have e : (Subgroup.centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer {g * u * g⁻¹} := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [conj_mul_conj', conj_mul_conj', hx]
    · intro h
      refine ⟨g⁻¹ * z * g, ?_, by group⟩
      calc g⁻¹ * z * g * u = g⁻¹ * (z * (g * u * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * u * g⁻¹ * z) * g := by rw [h]
        _ = u * (g⁻¹ * z * g) := by group
  rw [← e, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem two_pow_dvd_of_mul_eq {a b m : ℕ} (h : a * b = 2 ^ 38 * m) (hb0 : 0 < b)
    (hb : b < 2 ^ 12) : 2 ^ 27 ∣ a := by
  obtain ⟨k, b', hb', rfl⟩ := Nat.exists_eq_two_pow_mul_odd hb0.ne'
  have hk : k < 12 := by
    by_contra hk
    push Not at hk
    have h1 : 2 ^ 12 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h2 : 2 ^ k ≤ 2 ^ k * b' := Nat.le_mul_of_pos_right _ hb'.pos
    omega
  have h1 : 2 ^ 38 ∣ a * 2 ^ k * b' := ⟨m, by rw [mul_assoc, h]⟩
  have hcop : Nat.Coprime (2 ^ 38) b' := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hb')
  have h2 : 2 ^ 38 ∣ a * 2 ^ k := hcop.dvd_of_dvd_mul_right h1
  have h3 : 2 ^ (38 - k) * 2 ^ k ∣ a * 2 ^ k := by
    rwa [← pow_add, Nat.sub_add_cancel (by omega)]
  have h4 : 2 ^ (38 - k) ∣ a := Nat.dvd_of_mul_dvd_mul_right (by positivity) h3
  exact (pow_dvd_pow 2 (by omega)).trans h4

theorem rank_conj_inv
    (g y : Sbp) : ((βr (g * y * g⁻¹)) - 1).rank = ((βr y) - 1).rank := by
  have h := rank_conj g⁻¹ y
  rwa [inv_inv] at h

theorem qS_comm_code
    {a b : ℕ} (h : qS a * qS b = qS b * qS a) : qmul gArr a b = qmul gArr b a := by
  rw [qS_mul, qS_mul] at h
  exact qS_injOn (qmul_lt _ _) (qmul_lt _ _) h

theorem qmul_qinv_qmul
    {a n : ℕ} (hn : n < 2 ^ 23) : qmul gArr (qinv a) (qmul gArr a n) = n := by
  apply qS_injOn (qmul_lt _ _) hn
  rw [← qS_mul, ← qS_mul, qS_qinv, inv_mul_cancel_left]

theorem rank_qS_seven :
    ((βr (qS 7)) - 1).rank = 2168 := by
  rw [← rs3_eq]
  exact rank_four.2.2.2

theorem qS_seven_mul_self :
    qS 7 * qS 7 = 1 := sq_qS_one (.inr (.inr rfl))

theorem innerTyRank_eq_2168 {k : ℕ} (h : innerTyRank k = 2168) : k = 3 := by
  unfold innerTyRank at h
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> simp_all

theorem innerTy_eq_three
    {m : ℕ} (hm : m < 2 ^ 23) (h2 : qS m * qS m = 1)
    (hr : ((βr (qS m)) - 1).rank = 2168) : innerTy innerTab m = 3 := by
  obtain ⟨-, h1, h3⟩ := innerRank_spec hm
  have hne : innerTyRank (innerTy innerTab m) ≠ 1 := fun e => xs_ne_one' ((h1 e).symm.trans h2)
  have h4 := (h3 hne).2
  rw [hr] at h4
  exact innerTyRank_eq_2168 h4.symm

theorem mem_jClass_seven_of_innerTy
    {n : ℕ} (hn : n < 2 ^ 23) (h : innerTy innerTab n = 3) :
    qS n ∈ jClass (qS 7) := by
  rcases innerTy_spec hn with ⟨-, ht⟩ | ⟨-, ht⟩ | ⟨k, hk, ht, hmem⟩
  · rw [ht] at h
    exact absurd h (by decide)
  · rw [ht] at h
    exact absurd h (by decide)
  · have hk2 : k = 2 := by omega
    subst hk2
    exact mem_jClass_of (by decide) (qS_mem n) hmem

theorem mul_self_of_mem_jClass_seven
    {u : Sbp} (h : u ∈ jClass (qS 7)) : u * u = 1 := by
  obtain ⟨g, -, rfl⟩ := h
  rw [conj_mul_conj, qS_seven_mul_self]
  group

theorem rank_of_mem_jClass_seven
    {u : Sbp} (h : u ∈ jClass (qS 7)) :
    ((βr u) - 1).rank = 2168 := by
  rw [rank_beta_conj (isConj_of_mem_jClass h), rank_qS_seven]

theorem innerTy_eq_three_of_mem
    {n : ℕ} (hn : n < 2 ^ 23) (h : qS n ∈ jClass (qS 7)) :
    innerTy innerTab n = 3 :=
  innerTy_eq_three hn (mul_self_of_mem_jClass_seven h) (rank_of_mem_jClass_seven h)

theorem ne_one_of_rank_2168
    {t : Sbp} (hr : ((βr t) - 1).rank = 2168) : t ≠ 1 := by
  rintro rfl
  rw [rank_beta_one] at hr
  exact absurd hr (by decide)

theorem isConj_qS_seven_of_rank
    {w : Sbp} (hw2 : w * w = 1)
    (hwr : ((βr w) - 1).rank = 2168) : IsConj w (qS 7) := by
  have hord : orderOf w = 2 := orderOf_eq_prime (by rw [sq, hw2]) (ne_one_of_rank_2168 hwr)
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := four_classes co2_involution_input hord
  have e := rank_beta_conj hc
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · omega
  · omega
  · omega
  · rwa [rs3_eq] at hc

theorem mem_jClass_seven_of_rank
    {t : Sbp} (htQ : t ∈ Qs) (ht2 : t * t = 1)
    (hr : ((βr t) - 1).rank = 2168) : t ∈ jClass (qS 7) := by
  have hmem : t ∈ {t | t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1} := ⟨htQ, ht2, ne_one_of_rank_2168 hr⟩
  rw [invs_eq] at hmem
  obtain ⟨h1, h0, -, -⟩ := rank_four
  rcases hmem with ((h | h) | h) | h
  · have := rank_beta_conj (isConj_of_mem_jClass h)
    omega
  · have := rank_beta_conj (isConj_of_mem_jClass h)
    omega
  · have := rank_beta_conj (isConj_of_mem_jClass h)
    rw [rank_rs (by norm_num : 2 < 14)] at this
    have e : Native.repRanks.getD 2 0 = 2048 := rfl
    omega
  · rwa [rs3_eq] at h

theorem rank_labelS_mul_of_isConj
    {y : Sbp} (hy : IsConj y labelS)
    (hcy : y * labelS = labelS * y) (hne : y ≠ labelS) :
    ((βr (labelS * y)) - 1).rank = 2048 ∨ ((βr (labelS * y)) - 1).rank = 2158 := by
  obtain ⟨u, hu⟩ := exists_clabelS_eq ambientRootOrbitsHyp hy
  have hv : clabelS cv0 = sEquiv labelS := by rw [sEquiv_labelS, cS_inv, clabelS_cv0]
  have hne' : cv0 ≠ u := by
    rintro rfl
    exact hne (sEquiv.injective (hu.symm.trans hv))
  have hc : Commute (clabelS cv0) (clabelS u) := by
    rw [hv, hu]
    exact Commute.map (show Commute labelS y from hcy.symm) sEquiv
  have hprod : sEquiv (labelS * y) = clabelS cv0 * clabelS u := by rw [map_mul, hv, hu]
  rcases adj_or_dist_three_of_commute (diameter_three_rank_five_of_ambient ambientRootOrbitsHyp).1
    hne' hc with hadj | h3
  · exact .inl (rank_of_adj hadj hprod)
  · exact .inr (rank_of_dist_three h3 hprod)

theorem kClass_Jbar (t : Sbp) : {u | ∃ k ∈ Jbar.op, u = k * t * k⁻¹} = jClass t := by
  ext u
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k⁻¹, Jbar.op.inv_mem hk, by group⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g⁻¹, Jbar.op.inv_mem hg, by group⟩

theorem natCard_centralizer_xs_mul_ncard
    {t : Sbp} (ht : t ∈ Jbar.op) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set Sbp) ⊓ Subgroup.centralizer {xs}) *
      (jClass t).ncard = 2 ^ 41 * 161382375 := by
  have h := natCard_inf_centralizer_mul_ncard Jbar.op ht
  rw [kClass_Jbar, natCard_Jbar_op] at h
  rw [inf_comm, centralizer_xs_eq]
  exact h

theorem natCard_centralizer_q7_xs :
    Nat.card ↥(Subgroup.centralizer ({qS 7} : Set Sbp) ⊓ Subgroup.centralizer {xs}) =
      2 ^ 38 * 315 := by
  have h := natCard_centralizer_xs_mul_ncard (Ebar_le_Jbar (qS_mem 7))
  rw [← rs3_eq, ncard_jClass_rs3, rs3_eq] at h
  have e : (2 : ℕ) ^ 41 * 161382375 = 2 ^ 38 * 315 * 4098600 := by norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans e)

theorem tableSix_row_exists : ∀ i ∈ Finset.Icc 4 13, ∃ r ∈ tableSixRows,
    r.1 = i ∧ 8 ∣ r.2.2.1 ∧ IsRank r.2.1 := by
  decide

theorem eight_dvd_ncard_jClass_of_not_mem
    {t : Sbp} (htJ : t.unop ∈ Jbar) (ht2 : t * t = 1)
    (htQ : t ∉ Qs) : 8 ∣ (jClass t).ncard := by
  obtain ⟨i, hi, hti⟩ := exists_jClass_rs htJ ht2 htQ
  obtain ⟨⟨i', k, n, m, ρ, b⟩, hrow, hi', h8, hk⟩ := tableSix_row_exists i hi
  simp only at hi' h8 hk
  subst hi'
  obtain ⟨-, -, hmem, hn, -⟩ := native_table_six_classes.2.2.2 _ _ _ _ _ _ hrow
  rw [jClass_eq_of_mem hti, ncard_jClass_eq_mul hk hmem, hn]
  exact Dvd.dvd.mul_left h8 _

theorem not_two_pow_dvd_of_rank
    {t : Sbp} (htJ : t ∈ Jbar.op) (ht2 : t * t = 1)
    (hr : ((βr t) - 1).rank = 2168) :
    ¬ 2 ^ 39 ∣ Nat.card ↥(Subgroup.centralizer ({t} : Set Sbp) ⊓ Subgroup.centralizer {xs}) := by
  have h8 : 8 ∣ (jClass t).ncard := by
    by_cases htQ : t ∈ Qs
    · rw [jClass_eq_of_mem (mem_jClass_seven_of_rank htQ ht2 hr), ← rs3_eq, ncard_jClass_rs3]
      norm_num
    · exact eight_dvd_ncard_jClass_of_not_mem htJ ht2 htQ
  intro h39
  have h := Nat.mul_dvd_mul h39 h8
  rw [natCard_centralizer_xs_mul_ncard htJ] at h
  exact absurd h (by norm_num)

theorem zpowers_normal_of_comm {G : Type*} [Group G] {a : G} (ha : ∀ g, g * a = a * g) :
    (Subgroup.zpowers a).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  have hc : Commute g a := ha g
  rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  exact hn

theorem not_two_dvd_index_q7 :
    ¬ 2 ∣ ((Subgroup.centralizer ({qS 7} : Set Sbp) ⊓ Subgroup.centralizer {xs}).subgroupOf
      (Subgroup.centralizer {qS 7})).index := by
  set K := Subgroup.centralizer ({qS 7} : Set Sbp) with hK
  intro h2
  have hcard := Subgroup.card_mul_index
    ((Subgroup.centralizer ({qS 7} : Set Sbp) ⊓ Subgroup.centralizer {xs}).subgroupOf K)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
    natCard_centralizer_q7_xs] at hcard
  have hdvd : 2 ^ 39 ∣ Nat.card K := by
    rw [← hcard]
    obtain ⟨m, hm⟩ := h2
    rw [hm]
    exact ⟨315 * m, by ring⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 K) := inferInstance
  have hT : 2 ^ 39 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card hdvd
  set q7' : K := ⟨qS 7, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ with hq7'
  have hcen : ∀ g : K, g * q7' = q7' * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hnorm : (Subgroup.zpowers q7').Normal := zpowers_normal_of_comm hcen
  have hp7 : IsPGroup 2 (Subgroup.zpowers q7') := isPGroup_zpowers_of_pow_four
    (Subtype.ext (by
      show qS 7 ^ 4 = 1
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, qS_seven_mul_self, one_mul]))
  have h7T : q7' ∈ (T : Subgroup K) := hp7.le_sylow_of_normal T (Subgroup.mem_zpowers _)
  have hT'card : Nat.card ((T : Subgroup K).map K.subtype) = Nat.card T :=
    Subgroup.card_map_of_injective K.subtype_injective
  obtain ⟨P, hP⟩ := (T.isPGroup'.map K.subtype).exists_le_sylow
  obtain ⟨-, -, hall, -⟩ := native_sylow_two_center
  obtain ⟨-, z, -, -, hzx, hZ⟩ := hall P
  have hzmem := CFSG.Monster.mem_map_center_iff.1 (hZ ▸ Subgroup.mem_zpowers z)
  have h7P : qS 7 ∈ (P : Subgroup Sbp) := hP ⟨q7', h7T, rfl⟩
  have hTle : (T : Subgroup K).map K.subtype ≤
      Subgroup.centralizer ({qS 7} : Set Sbp) ⊓ Subgroup.centralizer {z} := fun x hx =>
    ⟨Subgroup.map_subtype_le _ hx, Subgroup.mem_centralizer_singleton_iff.2 (hzmem.2 x (hP hx))⟩
  have hd := Subgroup.card_dvd_of_le hTle
  obtain ⟨g, hg⟩ := isConj_iff.1 hzx
  rw [← natCard_inf_centralizer_conj g, hg, hT'card] at hd
  have htJ : g * qS 7 * g⁻¹ ∈ Jbar.op := by
    rw [← centralizer_xs_eq, Subgroup.mem_centralizer_singleton_iff, ← hg, conj_mul_conj',
      conj_mul_conj', hzmem.2 _ h7P]
  have ht2 : g * qS 7 * g⁻¹ * (g * qS 7 * g⁻¹) = 1 := by
    rw [conj_mul_conj', qS_seven_mul_self]
    group
  have htr : ((βr (g * qS 7 * g⁻¹)) - 1).rank = 2168 := by
    rw [rank_conj_inv, rank_qS_seven]
  exact not_two_pow_dvd_of_rank htJ ht2 htr (hT.trans hd)

theorem exists_conj_into_Jbar_q7
    {s : Sbp} (hs7 : s * qS 7 = qS 7 * s) (hs4 : s ^ 4 = 1) :
    ∃ h : Sbp, h * qS 7 = qS 7 * h ∧ (h * s * h⁻¹).unop ∈ Jbar := by
  have hsC : s ∈ Subgroup.centralizer ({qS 7} : Set Sbp) :=
    Subgroup.mem_centralizer_singleton_iff.2 hs7
  have hP := isPGroup_zpowers_of_pow_four
    (g := (⟨s, hsC⟩ : Subgroup.centralizer ({qS 7} : Set Sbp)))
    (Subtype.ext (by simpa using hs4))
  obtain ⟨g, hg⟩ := exists_conj_mem_of_not_dvd_index _ not_two_dvd_index_q7 hP
  have hmem := hg ⟨s, hsC⟩ (Subgroup.mem_zpowers _)
  rw [Subgroup.mem_subgroupOf] at hmem
  have h2 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hmem).2
  refine ⟨g, Subgroup.mem_centralizer_singleton_iff.1 g.2, ?_⟩
  rw [mem_Jbar_iff_comm]
  have h3 := congrArg MulOpposite.unop h2
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, unop_mul] at h3
  simpa [xs, mul_assoc] using h3

theorem i3Cert_parts :
    countBelow (frameA innerTab) (2 ^ 23) 0 = 2240 ∧
    ((fusePts6 (gA6 ()) 43 34560).toList.filter fun a =>
      commR6 innerTab (qmul gArr (qinv 10541) a)).length = 30240 ∧
    (fusePts6 (gA6 ()) 46090 64).all (fun a => !commR6 innerTab (qmul gArr (qinv 10541) a)) =
      true ∧
    commR6 innerTab 854 = true ∧ (fusePts6 (gA6 ()) 43 34560).contains (qmul gArr 10541 854) =
      true ∧
    (List.range 15).all (fixR6 (gA6 ())) = true ∧
    natCertOK (fAct (gA6 ())) 15 (fun p => decide (p < 2 ^ 23)) 854
      (natBfs (fAct (gA6 ())) 15 854 30241).1 (natBfs (fAct (gA6 ())) 15 854 30241).2.1
      (natBfs (fAct (gA6 ())) 15 854 30241).2.2.1 (natBfs (fAct (gA6 ())) 15 854 30241).2.2.2 =
      true ∧
    (natBfs (fAct (gA6 ())) 15 854 30241).1.size = 30240 := by
  have h := i3CertOK_eq_true
  simp only [i3CertOK, frameBOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

@[expose] def aSet :
    Set Sbp :=
  {t | t ∈ Qs ∧ t ∈ jClass (qS 1) ∧ t * qS 7 = qS 7 * t ∧ ((βr (t * qS 7)) - 1).rank = 2168}

theorem ncard_frameA_codes :
    {n | n < 2 ^ 23 ∧ frameA innerTab n = true}.ncard = 2240 := by
  have h := i3Cert_parts.1
  rw [countBelow_eq, Nat.zero_add] at h
  have hs : {n | n < 2 ^ 23 ∧ frameA innerTab n = true} =
      ↑((Finset.range (2 ^ 23)).filter fun n => frameA innerTab n = true) := by
    ext n
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
  rw [hs, Set.ncard_coe_finset]
  exact h

theorem ncard_aSet_le :
    aSet.ncard ≤ 2240 := by
  have hsub : aSet ⊆ qS '' {n | n < 2 ^ 23 ∧ frameA innerTab n = true} := by
    rintro t ⟨htQ, ht1, ht7, htr⟩
    obtain ⟨n, hn, rfl⟩ := exists_qS htQ
    refine ⟨n, ⟨hn, ?_⟩, rfl⟩
    have hc := qS_comm_code ht7
    have h2 : qS (qmul gArr n 7) * qS (qmul gArr n 7) = 1 := by
      rw [← qS_mul]
      calc qS n * qS 7 * (qS n * qS 7) = qS n * (qS 7 * qS n) * qS 7 := by group
        _ = qS n * (qS n * qS 7) * qS 7 := by rw [ht7]
        _ = 1 := by
          rw [← mul_assoc, mul_self_of_mem_jClass ht1, one_mul, qS_seven_mul_self]
    have hr3 : ((βr (qS (qmul gArr n 7))) - 1).rank = 2168 := by rw [← qS_mul]; exact htr
    simp only [frameA, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨innerTy_eq_one_of_mem hn ht1, hc⟩, innerTy_eq_three (qmul_lt _ _) h2 hr3⟩
  calc aSet.ncard ≤ (qS '' {n | n < 2 ^ 23 ∧ frameA innerTab n = true}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = 2240 := by
        rw [ncard_image_qS (fun n hn => hn.1), ncard_frameA_codes]

theorem mem_aSet_conj
    {k t : Sbp} (hk : k ∈ Subgroup.centralizer ({qS 7} : Set Sbp) ⊓
    Subgroup.centralizer {xs}) (ht : t ∈ aSet) : k * t * k⁻¹ ∈ aSet := by
  obtain ⟨hk7, hkx⟩ := hk
  have hkJ : k ∈ Jbar.op := by rw [← centralizer_xs_eq]; exact hkx
  have hk7' := Subgroup.mem_centralizer_singleton_iff.1 hk7
  have e7 : k * qS 7 * k⁻¹ = qS 7 := by rw [hk7']; group
  obtain ⟨htQ, ht1, ht7, htr⟩ := ht
  refine ⟨?_, conj_mem_jClass hkJ ht1, ?_, ?_⟩
  · have h := conj_mem_Qs (g := k⁻¹) (Jbar.op.inv_mem hkJ) htQ
    rwa [inv_inv] at h
  · rw [← e7, conj_mul_conj', conj_mul_conj', ht7]
  · rw [← e7, conj_mul_conj', rank_conj_inv, htr]

theorem two_pow_dvd_caseA
    {c : Sbp} (hcQ : c ∈ Qs) (hc : IsConj c labelS)
    (hc7 : c * qS 7 = qS 7 * c) (hr : ((βr (c * qS 7)) - 1).rank = 2168) :
    2 ^ 27 ∣ Nat.card ↥(Subgroup.centralizer ({c} : Set Sbp) ⊓ Subgroup.centralizer {qS 7}) := by
  set K := Subgroup.centralizer ({qS 7} : Set Sbp) ⊓ Subgroup.centralizer {xs} with hK
  have hcK : c ∈ K := ⟨Subgroup.mem_centralizer_singleton_iff.2 hc7, by
    rw [centralizer_xs_eq]; exact Ebar_le_Jbar hcQ⟩
  have h := natCard_inf_centralizer_mul_ncard K hcK
  rw [natCard_centralizer_q7_xs] at h
  have hcA : c ∈ aSet := ⟨hcQ, mem_jClass_of_isConj_labelS hcQ hc, hc7, hr⟩
  have hsub : {u | ∃ k ∈ K, u = k * c * k⁻¹} ⊆ aSet := by
    rintro u ⟨k, hk, rfl⟩
    exact mem_aSet_conj hk hcA
  have hle : {u | ∃ k ∈ K, u = k * c * k⁻¹}.ncard ≤ 2240 :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ncard_aSet_le
  have hpos : 0 < {u | ∃ k ∈ K, u = k * c * k⁻¹}.ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨c, 1, K.one_mem, by group⟩
  have h27 := two_pow_dvd_of_mul_eq h hpos (by omega)
  refine h27.trans (Subgroup.card_dvd_of_le fun x hx => ?_)
  exact ⟨hx.2, hx.1.1⟩

theorem rs6_mul_qS
    (n : ℕ) : rs 6 * qS n = cosetElt 6 (qmul gArr 10541 n) := by
  show hs 6 * qS 10541 * qS n = hs 6 * qS (qmul gArr 10541 n)
  rw [mul_assoc, qS_mul]

theorem qS_mul_rs6
    (n : ℕ) :
    qS n * rs 6 = cosetElt 6 (qmul gArr (autApply gArr (liftImgsK 6).toArray n) 10541) := by
  show qS n * (hs 6 * qS 10541) =
    hs 6 * qS (qmul gArr (autApply gArr (liftImgsK 6).toArray n) 10541)
  rw [← qS_mul, ← conj_hs_qS (.inl rfl)]
  group

theorem comm_rs6_iff
    {n : ℕ} : qS n * rs 6 = rs 6 * qS n ↔
    qmul gArr (autApply gArr (liftImgsK 6).toArray n) 10541 = qmul gArr 10541 n := by
  rw [qS_mul_rs6, rs6_mul_qS]
  constructor
  · intro h
    exact qS_injOn (qmul_lt _ _) (qmul_lt _ _) (mul_left_cancel h)
  · intro h
    rw [h]

theorem commR6_iff
    {n : ℕ} (hn : n < 2 ^ 23) :
    commR6 innerTab n = true ↔ qS n ∈ jClass (qS 7) ∧ qS n * rs 6 = rs 6 * qS n := by
  rw [comm_rs6_iff]
  simp only [commR6, Bool.and_eq_true, beq_iff_eq, liftImgsN_eq]
  constructor
  · rintro ⟨h3, hc⟩
    exact ⟨mem_jClass_seven_of_innerTy hn h3, hc⟩
  · rintro ⟨h7, hc⟩
    exact ⟨innerTy_eq_three_of_mem hn h7, hc⟩

@[expose] def bSet :
    Set Sbp :=
  {t | t ∈ Qs ∧ t ∈ jClass (qS 7) ∧ t * rs 6 = rs 6 * t ∧ rs 6 * t ∈ jClass (rs 4)}

theorem fusePts6_r4 : fusePts6 (gA6 ()) 43 34560 = (fuseCert 6 (270, 34560, 43)).1 := rfl

theorem fusePts6_r8 : fusePts6 (gA6 ()) 46090 64 = (fuseCert 6 (1, 64, 46090)).1 := rfl

theorem rs4_eq :
    rs 4 = cosetElt 6 43 := rfl

theorem rec4_mem : ((270, 34560, 43) : ℕ × ℕ × ℕ) ∈ fusionRecsN 6 := by
  rw [fusionRecs_eq.1]
  simp

theorem rec8_mem : ((1, 64, 46090) : ℕ × ℕ × ℕ) ∈ fusionRecsN 6 := by
  rw [fusionRecs_eq.1]
  simp

theorem validK6_of
    {m : ℕ} (hm : m < 2 ^ 23) (h2 : cosetElt 6 m * cosetElt 6 m = 1) :
    validK 6 m = true := by
  simp only [validK, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hm, (cosetElt_sq_eq_one_iff (.inl rfl)).1 h2⟩

theorem cosetInv6_of
    {m : ℕ} (h2 : cosetElt 6 m * cosetElt 6 m = 1) : cosetElt 6 m ∈ cosetInv 6 :=
  ⟨⟨qS m, qS_mem m, rfl⟩, h2⟩

theorem mem_jClass_rs4_iff
    {m : ℕ} (hm : m < 2 ^ 23) (h2 : cosetElt 6 m * cosetElt 6 m = 1) :
    cosetElt 6 m ∈ jClass (rs 4) ↔ (fusePts6 (gA6 ()) 43 34560).contains m = true := by
  have hf : cosetElt 6 m ∈ fClass 6 (cosetElt 6 43) ↔
      (fuseCert 6 (270, 34560, 43)).1.contains m = true :=
    (fOrbit_facts (.inl rfl) rec4_mem).2.2.2 m (validK6_of hm h2)
  have hi : jClass (rs 4) ∩ cosetInv 6 = fClass 6 (rs 4) :=
    jClass_inter_cosetInv (.inl rfl) rec4_mem (by decide) rfl
  rw [fusePts6_r4, ← hf, ← rs4_eq, ← hi]
  exact ⟨fun hj => ⟨hj, cosetInv6_of h2⟩, fun h => h.1⟩

theorem ncard_bSet_le :
    bSet.ncard ≤ 30240 := by
  set L := (fusePts6 (gA6 ()) 43 34560).toList.filter fun a =>
    commR6 innerTab (qmul gArr (qinv 10541) a) with hL
  have hsub : bSet ⊆ (fun a => qS (qmul gArr (qinv 10541) a)) '' {a | a ∈ L} := by
    rintro t ⟨htQ, ht7, htc, ht4⟩
    obtain ⟨n, hn, rfl⟩ := exists_qS htQ
    have h2 : rs 6 * qS n * (rs 6 * qS n) = 1 := by
      calc rs 6 * qS n * (rs 6 * qS n) = rs 6 * (qS n * rs 6) * qS n := by group
        _ = rs 6 * (rs 6 * qS n) * qS n := by rw [htc]
        _ = 1 := by
          rw [← mul_assoc, rs6_mul_self, one_mul, mul_self_of_mem_jClass_seven ht7]
    rw [rs6_mul_qS] at h2 ht4
    have hcont := (mem_jClass_rs4_iff (qmul_lt _ _) h2).1 ht4
    refine ⟨qmul gArr 10541 n, ?_, ?_⟩
    swap
    · show qS (qmul gArr (qinv 10541) (qmul gArr 10541 n)) = qS n
      rw [qmul_qinv_qmul hn]
    show qmul gArr 10541 n ∈ L
    rw [hL, List.mem_filter]
    refine ⟨Array.mem_toList_iff.2 (Array.contains_iff_mem.1 hcont), ?_⟩
    rw [qmul_qinv_qmul hn]
    exact (commR6_iff hn).2 ⟨ht7, htc⟩
  have hfin : {a | a ∈ L} = ↑L.toFinset := by
    ext a
    simp
  calc bSet.ncard ≤ ((fun a => qS (qmul gArr (qinv 10541) a)) '' {a | a ∈ L}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ {a | a ∈ L}.ncard := Set.ncard_image_le (List.finite_toSet L)
    _ = L.toFinset.card := by rw [hfin, Set.ncard_coe_finset]
    _ ≤ L.length := List.toFinset_card_le L
    _ = 30240 := i3Cert_parts.2.1

@[expose] def fElt
    (j : ℕ) : Sbp := centElt 6 j * qS (eCodes.getD j 0)

theorem fElt_mem_Jbar
    {j : ℕ} (hj : j < 15) : fElt j ∈ Jbar.op :=
  Jbar.op.mul_mem (centElt_mem_Jbar (.inl rfl) hj) (Ebar_le_Jbar (qS_mem _))

theorem gA6_getD {j : ℕ} (hj : j < 15) :
    (gA6 ()).getD j #[] = wordAut (genInvImgs ()) (centWordN 6 j) :=
  centAuts_getD hj

theorem ds6_getD {j : ℕ} (hj : j < 15) : ds6.getD j 0 = deltaN 6 j :=
  deltas_getD hj

theorem conj_fElt_qS
    {j : ℕ} (hj : j < 15) (n : ℕ) :
    (fElt j)⁻¹ * qS n * fElt j = qS (fAct (gA6 ()) j n) := by
  have hc := conj_qS (centElt_mem_Jbar (.inl rfl) hj)
    (conj_wordS' (centWordN_letters (.inl rfl) hj)).1 n
  have e : (fElt j)⁻¹ * qS n * fElt j =
      (qS (eCodes.getD j 0))⁻¹ * ((centElt 6 j)⁻¹ * qS n * centElt 6 j) * qS (eCodes.getD j 0) := by
    rw [fElt]
    group
  rw [e, hc, fAct, gA6_getD hj, ← qS_mul, ← qS_mul, qS_qinv]

theorem qS_conj_cosetElt6
    (e b : ℕ) :
    (qS e)⁻¹ * cosetElt 6 b * qS e =
      cosetElt 6 (qmul gArr (qinv (autApply gArr (liftImgsK 6).toArray e)) (qmul gArr b e)) := by
  have h := conj_hs_qS (.inl rfl) e
  show (qS e)⁻¹ * (hs 6 * qS b) * qS e =
    hs 6 * qS (qmul gArr (qinv (autApply gArr (liftImgsK 6).toArray e)) (qmul gArr b e))
  rw [← qS_mul, ← qS_mul, qS_qinv, ← h]
  group

theorem fElt_comm_rs6
    {j : ℕ} (hj : j < 15) : (fElt j)⁻¹ * rs 6 * fElt j = rs 6 := by
  have hok := (cosetOK_parts (.inl rfl)).2.2.2.2.2.2.2 j hj
  have hf := fuse_act (.inl rfl) hj hok 10541
  rw [toConjAct_smul, inv_inv] at hf
  have hfix : fixR6 (gA6 ()) j = true := by
    have h := i3Cert_parts.2.2.2.2.2.1
    simp only [List.all_eq_true, List.mem_range] at h
    exact h j hj
  simp only [fixR6, beq_iff_eq, gA6_getD hj, ds6_getD hj, liftImgsN_eq] at hfix
  have e : (fElt j)⁻¹ * rs 6 * fElt j = (qS (eCodes.getD j 0))⁻¹ *
      ((centElt 6 j)⁻¹ * cosetElt 6 10541 * centElt 6 j) * qS (eCodes.getD j 0) := by
    rw [fElt]
    show (centElt 6 j * qS (eCodes.getD j 0))⁻¹ * cosetElt 6 10541 *
      (centElt 6 j * qS (eCodes.getD j 0)) = _
    group
  rw [e, ← hf, qS_conj_cosetElt6, hfix]
  rfl

@[expose] def kR6 :
    Subgroup Sbp := Subgroup.centralizer {rs 6} ⊓ Subgroup.centralizer {xs}

theorem fElt_inv_mem_kR6
    {j : ℕ} (hj : j < 15) : (fElt j)⁻¹ ∈ kR6 := by
  refine kR6.inv_mem ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
  · have h := fElt_comm_rs6 hj
    calc fElt j * rs 6 = fElt j * ((fElt j)⁻¹ * rs 6 * fElt j) := by rw [h]
      _ = rs 6 * fElt j := by group
  · rw [centralizer_xs_eq]
    exact fElt_mem_Jbar hj

theorem mem_bSet_conj
    {k t : Sbp} (hk : k ∈ kR6) (ht : t ∈ bSet) : k * t * k⁻¹ ∈ bSet := by
  obtain ⟨hk6, hkx⟩ := hk
  have hkJ : k ∈ Jbar.op := by rw [← centralizer_xs_eq]; exact hkx
  have e6 : k * rs 6 * k⁻¹ = rs 6 := by rw [Subgroup.mem_centralizer_singleton_iff.1 hk6]; group
  obtain ⟨htQ, ht7, htc, ht4⟩ := ht
  refine ⟨?_, conj_mem_jClass hkJ ht7, ?_, ?_⟩
  · have h := conj_mem_Qs (g := k⁻¹) (Jbar.op.inv_mem hkJ) htQ
    rwa [inv_inv] at h
  · rw [← e6, conj_mul_conj', conj_mul_conj', htc]
  · rw [← e6, conj_mul_conj']
    exact conj_mem_jClass hkJ ht4

theorem qS854_mem_bSet :
    qS 854 ∈ bSet := by
  obtain ⟨-, -, -, h854, hcont, -⟩ := i3Cert_parts
  obtain ⟨h7, hc⟩ := (commR6_iff (by norm_num)).1 h854
  have h2 : rs 6 * qS 854 * (rs 6 * qS 854) = 1 := by
    calc rs 6 * qS 854 * (rs 6 * qS 854) = rs 6 * (qS 854 * rs 6) * qS 854 := by group
      _ = rs 6 * (rs 6 * qS 854) * qS 854 := by rw [hc]
      _ = 1 := by
        rw [← mul_assoc, rs6_mul_self, one_mul, mul_self_of_mem_jClass_seven h7]
  rw [rs6_mul_qS] at h2
  refine ⟨qS_mem _, h7, hc, ?_⟩
  rw [rs6_mul_qS]
  exact (mem_jClass_rs4_iff (qmul_lt _ _) h2).2 hcont

theorem exists_conj_of_mem_bSet
    {b : Sbp} (hb : b ∈ bSet) :
    ∃ k ∈ kR6, b = k * qS 854 * k⁻¹ := by
  obtain ⟨-, -, -, -, -, -, hcert, hsize⟩ := i3Cert_parts
  have hact : ∀ j < 15, ∀ a, decide (a < 2 ^ 23) = true →
      qS (fAct (gA6 ()) j a) = (fun j => toConjAct (fElt j)⁻¹) j • qS a := by
    intro j hj a _
    rw [toConjAct_smul, inv_inv, conj_fElt_qS hj]
  have hinj : ∀ a b, decide (a < 2 ^ 23) = true → decide (b < 2 ^ 23) = true →
      qS a = qS b → a = b := fun a b ha hb h =>
    qS_injOn (of_decide_eq_true ha) (of_decide_eq_true hb) h
  obtain ⟨horb, hnc, -, -⟩ := orbit_of_nativeCert (dec := qS) hcert hact hinj
  set O := MulAction.orbit (Subgroup.closure
    ((fun j => toConjAct (fElt j)⁻¹) '' {k | k < 15})) (qS 854) with hO
  have hcl : Subgroup.closure ((fun j => toConjAct (fElt j)⁻¹) '' {k | k < 15}) ≤
      kR6.map (toConjAct : Sbp ≃* ConjAct Sbp).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨(fElt j)⁻¹, fElt_inv_mem_kR6 hj, rfl⟩
  have hOk : ∀ x ∈ O, ∃ k ∈ kR6, x = k * qS 854 * k⁻¹ := by
    rintro x ⟨⟨c, hc⟩, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hcl hc
    refine ⟨k, hk, ?_⟩
    show (toConjAct k : ConjAct Sbp) • qS 854 = k * qS 854 * k⁻¹
    rw [toConjAct_smul]
  have hOB : O ⊆ bSet := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hOk x hx
    exact mem_bSet_conj hk qS854_mem_bSet
  have hOeq : O = bSet := Set.eq_of_subset_of_ncard_le hOB
    (by rw [hnc, hsize]; exact ncard_bSet_le) (Set.toFinite _)
  rw [← hOeq] at hb
  exact hOk b hb

theorem kClass_eq_bSet
    {q : Sbp} (hq : q ∈ bSet) : {u | ∃ k ∈ kR6, u = k * q * k⁻¹} = bSet := by
  obtain ⟨k₀, hk₀, rfl⟩ := exists_conj_of_mem_bSet hq
  ext u
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact mem_bSet_conj hk hq
  · intro hu
    obtain ⟨k, hk, rfl⟩ := exists_conj_of_mem_bSet hu
    refine ⟨k * k₀⁻¹, kR6.mul_mem hk (kR6.inv_mem hk₀), by group⟩

theorem ncard_bSet :
    bSet.ncard = 30240 := by
  refine le_antisymm ncard_bSet_le ?_
  obtain ⟨-, -, -, -, -, -, hcert, hsize⟩ := i3Cert_parts
  have hact : ∀ j < 15, ∀ a, decide (a < 2 ^ 23) = true →
      qS (fAct (gA6 ()) j a) = (fun j => toConjAct (fElt j)⁻¹) j • qS a := by
    intro j hj a _
    rw [toConjAct_smul, inv_inv, conj_fElt_qS hj]
  have hinj : ∀ a b, decide (a < 2 ^ 23) = true → decide (b < 2 ^ 23) = true →
      qS a = qS b → a = b := fun a b ha hb h =>
    qS_injOn (of_decide_eq_true ha) (of_decide_eq_true hb) h
  obtain ⟨-, hnc, -, -⟩ := orbit_of_nativeCert (dec := qS) hcert hact hinj
  have hsub : MulAction.orbit (Subgroup.closure
      ((fun j => toConjAct (fElt j)⁻¹) '' {k | k < 15})) (qS 854) ⊆ bSet := by
    rintro x ⟨⟨c, hc⟩, rfl⟩
    have hcl : Subgroup.closure ((fun j => toConjAct (fElt j)⁻¹) '' {k | k < 15}) ≤
        kR6.map (toConjAct : Sbp ≃* ConjAct Sbp).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨(fElt j)⁻¹, fElt_inv_mem_kR6 hj, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hcl hc
    show (toConjAct k : ConjAct Sbp) • qS 854 ∈ bSet
    rw [toConjAct_smul]
    exact mem_bSet_conj hk qS854_mem_bSet
  rw [← hsize, ← hnc]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem rs6_mem_kR6_q
    {q : Sbp} (hq : q ∈ bSet) : q ∈ kR6 := by
  obtain ⟨hqQ, -, hqc, -⟩ := hq
  refine ⟨Subgroup.mem_centralizer_singleton_iff.2 hqc, ?_⟩
  rw [centralizer_xs_eq]
  exact Ebar_le_Jbar hqQ

theorem natCard_kR6_inf_centralizer
    {q : Sbp} (hq : q ∈ bSet) :
    Nat.card ↥(kR6 ⊓ Subgroup.centralizer {q}) = 3221225472 := by
  have h := natCard_inf_centralizer_mul_ncard kR6 (rs6_mem_kR6_q hq)
  have hk : Nat.card kR6 = 97409858273280 := natCard_centralizer_rs6_xs
  rw [kClass_eq_bSet hq, ncard_bSet, hk] at h
  have e : (97409858273280 : ℕ) = 3221225472 * 30240 := by norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans e)

theorem qS_eq_of_rs6_mul
    {q : Sbp} {a : ℕ} (h : rs 6 * q = cosetElt 6 a) :
    q = qS (qmul gArr (qinv 10541) a) := by
  rw [← qS_mul, qS_qinv]
  calc q = (qS 10541)⁻¹ * (hs 6)⁻¹ * (rs 6 * q) := by
        show q = (qS 10541)⁻¹ * (hs 6)⁻¹ * (hs 6 * qS 10541 * q)
        group
    _ = (qS 10541)⁻¹ * qS a := by
        rw [h]
        show (qS 10541)⁻¹ * (hs 6)⁻¹ * (hs 6 * qS a) = _
        group

theorem mem_bSet_of_rank
    {q : Sbp} (hqQ : q ∈ Qs) (hq7 : q ∈ jClass (qS 7))
    (hqc : q * rs 6 = rs 6 * q) (hr : ((βr (rs 6 * q)) - 1).rank = 2168) : q ∈ bSet := by
  refine ⟨hqQ, hq7, hqc, ?_⟩
  have h2 : rs 6 * q * (rs 6 * q) = 1 := by
    calc rs 6 * q * (rs 6 * q) = rs 6 * (q * rs 6) * q := by group
      _ = rs 6 * (rs 6 * q) * q := by rw [hqc]
      _ = 1 := by rw [← mul_assoc, rs6_mul_self, one_mul, mul_self_of_mem_jClass_seven hq7]
  have hinv : rs 6 * q ∈ cosetInv 6 := ⟨⟨qS 10541 * q, Qs.mul_mem (qS_mem _) hqQ, by
    show hs 6 * qS 10541 * q = hs 6 * (qS 10541 * q)
    rw [mul_assoc]⟩, h2⟩
  obtain ⟨r, hrec, hmem⟩ := cover_fClass (.inl rfl) hinv
  rw [fusionRecs_eq.1] at hrec
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrec
  have hrank : ∀ i < 14, rs 6 * q ∈ fClass 6 (rs i) →
      ((βr (rs 6 * q)) - 1).rank = Native.repRanks.getD i 0 := fun i hi hf => by
    rw [rank_beta_conj (isConj_of_mem_jClass (fClass_subset_jClass (.inl rfl) _ hf)),
      rank_rs hi]
  rcases hrec with rfl | rfl | rfl | rfl | rfl
  · exact fClass_subset_jClass (.inl rfl) _ hmem
  · have := hrank 5 (by norm_num) hmem
    rw [hr] at this
    exact absurd this (by decide)
  · have := hrank 6 (by norm_num) hmem
    rw [hr] at this
    exact absurd this (by decide)
  · have := hrank 7 (by norm_num) hmem
    rw [hr] at this
    exact absurd this (by decide)
  · exfalso
    obtain ⟨a, hva, -, ha⟩ := (fOrbit_facts (.inl rfl) rec8_mem).2.2.1 _ hmem
    have hcont := ((fOrbit_facts (.inl rfl) rec8_mem).2.2.2 a hva).1 (by rw [← ha]; exact hmem)
    rw [← fusePts6_r8] at hcont
    have hall := i3Cert_parts.2.2.1
    rw [Array.all_eq_true] at hall
    obtain ⟨i, hi, hia⟩ := Array.mem_iff_getElem.1 (Array.contains_iff_mem.1 hcont)
    have h1 := hall i hi
    rw [hia] at h1
    have hqa := qS_eq_of_rs6_mul ha
    have hc' : commR6 innerTab (qmul gArr (qinv 10541) a) = true := by
      rw [hqa] at hq7 hqc
      exact (commR6_iff (qmul_lt _ _)).2 ⟨hq7, hqc⟩
    rw [hc'] at h1
    exact absurd h1 (by decide)

theorem two_pow_dvd_caseB
    {c : Sbp} (hcJ : c.unop ∈ Jbar) (hcQ : c ∉ Qs) (hc : IsConj c labelS)
    (hc7 : c * qS 7 = qS 7 * c) (hr : ((βr (c * qS 7)) - 1).rank = 2168) :
    2 ^ 27 ∣ Nat.card ↥(Subgroup.centralizer ({c} : Set Sbp) ⊓ Subgroup.centralizer {qS 7}) := by
  have hc2 := mul_self_of_isConj_labelS hc
  obtain ⟨i, hi, hci⟩ := exists_jClass_rs hcJ hc2 hcQ
  have hi6 : i = 6 := by
    have := rank_beta_conj (isConj_of_mem_jClass hci)
    rw [rank_of_isConj_labelS hc, rank_rs (by simp only [Finset.mem_Icc] at hi; omega)] at this
    exact rs_rank_eq_1860 hi this.symm
  subst hi6
  obtain ⟨g, hg, hgc⟩ := hci
  have e6 : g * c * g⁻¹ = rs 6 := by rw [hgc]; group
  rw [← natCard_inf_centralizer_conj g, e6]
  have hq : g * qS 7 * g⁻¹ ∈ bSet := by
    refine mem_bSet_of_rank ?_ (conj_mem_jClass hg (mem_jClass_self _)) ?_ ?_
    · have h := conj_mem_Qs (g := g⁻¹) (Jbar.op.inv_mem hg) (qS_mem 7)
      rwa [inv_inv] at h
    · rw [← e6, conj_mul_conj', conj_mul_conj', hc7]
    · rw [← e6, conj_mul_conj', rank_conj_inv, hr]
  have h := natCard_kR6_inf_centralizer hq
  have hle : kR6 ⊓ Subgroup.centralizer {g * qS 7 * g⁻¹} ≤
      Subgroup.centralizer ({rs 6} : Set Sbp) ⊓ Subgroup.centralizer {g * qS 7 * g⁻¹} :=
    fun x hx => ⟨hx.1.1, hx.2⟩
  refine Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le hle)
  rw [h]
  norm_num

theorem two_pow_dvd_of_rank_pair
    {c y : Sbp} (hc : IsConj c labelS) (hy2 : y * y = 1)
    (hcy : y * c = c * y) (hry : ((βr y) - 1).rank = 2168)
    (hrcy : ((βr (c * y)) - 1).rank = 2168) :
    2 ^ 27 ∣ Nat.card ↥(Subgroup.centralizer ({c} : Set Sbp) ⊓ Subgroup.centralizer {y}) := by
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 (isConj_qS_seven_of_rank hy2 hry)
  rw [← natCard_inf_centralizer_conj g₁, hg₁]
  have hc₁l : IsConj (g₁ * c * g₁⁻¹) labelS := (isConj_iff.2 ⟨g₁⁻¹, by group⟩).trans hc
  have hc₁7 : g₁ * c * g₁⁻¹ * qS 7 = qS 7 * (g₁ * c * g₁⁻¹) := by
    rw [← hg₁, conj_mul_conj', conj_mul_conj', hcy]
  have hr₁ : ((βr (g₁ * c * g₁⁻¹ * qS 7)) - 1).rank = 2168 := by
    rw [← hg₁, conj_mul_conj', rank_conj_inv, hrcy]
  have hc₁2 := mul_self_of_isConj_labelS hc₁l
  have hc₁4 : (g₁ * c * g₁⁻¹) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hc₁2, one_mul]
  obtain ⟨h, hh7, hJ⟩ := exists_conj_into_Jbar_q7 hc₁7 hc₁4
  have e7 : h * qS 7 * h⁻¹ = qS 7 := by rw [hh7]; group
  rw [← natCard_inf_centralizer_conj h, e7]
  set c₂ := h * (g₁ * c * g₁⁻¹) * h⁻¹ with hc₂
  have hc₂l : IsConj c₂ labelS := (isConj_iff.2 ⟨h⁻¹, by rw [hc₂]; group⟩).trans hc₁l
  have hc₂7 : c₂ * qS 7 = qS 7 * c₂ := by
    rw [hc₂, ← e7, conj_mul_conj', conj_mul_conj', hc₁7]
  have hr₂ : ((βr (c₂ * qS 7)) - 1).rank = 2168 := by
    rw [hc₂, ← e7, conj_mul_conj', rank_conj_inv, hr₁]
  by_cases hQ : c₂ ∈ Qs
  · exact two_pow_dvd_caseA hQ hc₂l hc₂7 hr₂
  · exact two_pow_dvd_caseB hJ hQ hc₂l hc₂7 hr₂

theorem index_centralizer_xhatH :
    (Subgroup.centralizer ({xhatH} : Set (vStab cv0))).index = 3968055 := by
  have h := Subgroup.card_mul_index (Subgroup.centralizer ({xhatH} : Set (vStab cv0)))
  rw [natCard_vStab_eq, natCard_centralizer_vStab, sEquiv_symm_xhatH,
    natCard_centralizer_labelS_xs] at h
  have e : (77148607752437760 : ℕ) * 3968055 = 306129918735099415756800 := by norm_num
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) (h.trans e.symm)

theorem not_two_dvd_index_xhatH :
    ¬ 2 ∣ (Subgroup.centralizer ({xhatH} : Set (vStab cv0))).index := by
  rw [index_centralizer_xhatH]
  norm_num

theorem finite_vStab_cv0 :
    Finite (vStab cv0) := Finite.of_injective _ Subtype.val_injective

theorem isPGroup_zpowers_of_mul_self {G : Type*} [Group G] {u : G} (hu2 : u * u = 1) :
    IsPGroup 2 (Subgroup.zpowers u) :=
  isPGroup_zpowers_of_pow_four (by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hu2, one_mul])

theorem exists_conj_into_P1
    {u : vStab cv0} (hu2 : u * u = 1) :
    ∃ g : vStab cv0, g * u * g⁻¹ * xhatH = xhatH * (g * u * g⁻¹) := by
  have := finite_vStab_cv0
  obtain ⟨g, hg⟩ := exists_conj_mem_of_not_dvd_index _ not_two_dvd_index_xhatH
    (isPGroup_zpowers_of_mul_self hu2)
  exact ⟨g, Subgroup.mem_centralizer_singleton_iff.1 (hg u (Subgroup.mem_zpowers u))⟩

theorem two_pow_dvd_of_rkH_2048
    {u : vStab cv0} (hu2 : u * u = 1) (hr : rkH u = 2048) :
    2 ^ 27 ∣ Nat.card (Subgroup.centralizer ({u} : Set (vStab cv0))) := by
  rcases natCard_centralizer_of_rkH_2048 hu2 hr with ⟨-, h⟩ | ⟨-, h⟩
  · rw [h]
    norm_num
  · rw [h]
    norm_num

theorem cV0_mul_mul_self
    {u : vStab cv0} (hu2 : u * u = 1) : cV0 * u * (cV0 * u) = 1 := by
  rw [mul_assoc, ← mul_assoc u, ← commute_cV0 u, mul_assoc, hu2, mul_one, cV0_mul_self]

theorem two_pow_dvd_of_mem_P1
    (h2C : OuterTwoC) {u : vStab cv0}
    (hux : u * xhatH = xhatH * u) (hu : u ∈ commutator (vStab cv0)) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : 2 ^ 27 ∣ Nat.card (Subgroup.centralizer ({u} : Set (vStab cv0))) := by
  set y := sEquiv.symm (u : Shat) with hy
  have hy2 : y * y = 1 := mul_self_symm hu2
  have hy1 : y ≠ 1 := by
    intro h
    apply hu1
    apply Subtype.ext
    rw [Subgroup.coe_one, ← MulEquiv.apply_symm_apply sEquiv (u : Shat), ← hy, h, map_one]
  have hyc : y * labelS = labelS * y := commute_labelS_of_mem u
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [sq, hy2]) hy1
  have hcu2 := cV0_mul_mul_self hu2
  have h2048c : rkH (cV0 * u) = 2048 →
      2 ^ 27 ∣ Nat.card (Subgroup.centralizer ({u} : Set (vStab cv0))) := fun h => by
    rw [← centralizer_cV0_mul]
    exact two_pow_dvd_of_rkH_2048 hcu2 h
  have hcy : rkH (cV0 * u) = ((βr (labelS * y)) - 1).rank := rkH_cV0_mul u
  obtain ⟨i, ⟨hi, hci⟩, -⟩ := four_classes co2_involution_input hord
  have hry := rank_beta_conj hci
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  have hrk : rkH u = ((βr y) - 1).rank := rfl
  rcases hi with rfl | rfl | rfl | rfl
  ·
    have hyl : IsConj y labelS := isConj_labelS_of_rank hord (hry.trans h1)
    by_cases hyc0 : y = labelS
    · have hu0 : u = cV0 := by
        apply Subtype.ext
        rw [← MulEquiv.apply_symm_apply sEquiv (u : Shat), ← hy, hyc0, sEquiv_labelS_eq_cV0]
      have htop : Subgroup.centralizer ({u} : Set (vStab cv0)) = ⊤ := by
        rw [hu0, eq_top_iff]
        intro z _
        exact Subgroup.mem_centralizer_singleton_iff.2 (commute_cV0 z).symm
      rw [htop, Subgroup.card_top, natCard_vStab_eq]
      norm_num
    · rcases rank_labelS_mul_of_isConj hyl hyc hyc0 with h | h
      · exact h2048c (hcy.trans h)
      · exact absurd hu (h2C u hux hu2 (.inr (hcy.trans h)))
  ·
    exact two_pow_dvd_of_rkH_2048 hu2 (hrk.trans (hry.trans h0))
  ·
    exact absurd hu (h2C u hux hu2 (.inl (hrk.trans (hry.trans h5))))
  ·
    have hry' : ((βr y) - 1).rank = 2168 := hry.trans h3
    have hw2 : labelS * y * (labelS * y) = 1 := by
      calc labelS * y * (labelS * y) = labelS * (y * labelS) * y := by group
        _ = labelS * (labelS * y) * y := by rw [hyc]
        _ = 1 := by rw [← mul_assoc, labelS_mul_self, one_mul, hy2]
    have hw1 : labelS * y ≠ 1 := by
      intro h
      have : y = labelS := by
        calc y = labelS * (labelS * y) := by rw [← mul_assoc, labelS_mul_self, one_mul]
          _ = labelS := by rw [h, mul_one]
      rw [this, rank_labelS] at hry'
      exact absurd hry' (by decide)
    have hword : orderOf (labelS * y) = 2 := orderOf_eq_prime (by rw [sq, hw2]) hw1
    obtain ⟨j, ⟨hj, hcj⟩, -⟩ := four_classes co2_involution_input hword
    have hrw := rank_beta_conj hcj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl
    ·
      exfalso
      have hwl : IsConj (labelS * y) labelS := isConj_labelS_of_rank hword (hrw.trans h1)
      have hwc : labelS * y * labelS = labelS * (labelS * y) := by rw [mul_assoc, hyc]
      have hwne : labelS * y ≠ labelS := by
        intro h
        apply hy1
        calc y = labelS * (labelS * y) := by rw [← mul_assoc, labelS_mul_self, one_mul]
          _ = 1 := by rw [h, labelS_mul_self]
      have hll : labelS * (labelS * y) = y := by rw [← mul_assoc, labelS_mul_self, one_mul]
      rcases rank_labelS_mul_of_isConj hwl hwc hwne with h | h
      · rw [hll, hry'] at h
        exact absurd h (by decide)
      · rw [hll, hry'] at h
        exact absurd h (by decide)
    · exact h2048c (hcy.trans (hrw.trans h0))
    · exact absurd hu (h2C u hux hu2 (.inr (hcy.trans (hrw.trans h5))))
    · rw [natCard_centralizer_vStab]
      exact two_pow_dvd_of_rank_pair (IsConj.refl labelS) hy2 hyc hry' (hrw.trans h3)

theorem inner_involution_centralizer_two_pow_of
    (h2C : OuterTwoC) {u : vStab cv0}
    (hu : u ∈ commutator (vStab cv0)) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    2 ^ 27 ∣ Nat.card (Subgroup.centralizer ({u} : Set (vStab cv0))) := by
  obtain ⟨g, hg⟩ := exists_conj_into_P1 hu2
  rw [← natCard_centralizer_conj g]
  refine two_pow_dvd_of_mem_P1 h2C hg (Subgroup.Normal.conj_mem inferInstance u hu g) ?_ ?_
  · rw [conj_mul_conj', hu2]
    group
  · intro h
    apply hu1
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group

theorem outerTwoC :

    OuterTwoC := fun _ _ hy2 hr => not_mem_commutator_of_rank_2158 hy2 hr

theorem inner_involution_centralizer_two_pow
    {u : vStab cv0}
    (hu : u ∈ commutator (vStab cv0)) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    2 ^ 27 ∣ Nat.card (Subgroup.centralizer ({u} : Set (vStab cv0))) :=
  inner_involution_centralizer_two_pow_of outerTwoC hu hu2 hu1

theorem inner_involution_he
    {X : Subgroup (vStab cv0)} (hX : Nat.card X = 2 ^ 26) :
    ∀ u ∈ commutator (vStab cv0), u * u = 1 → u ≠ 1 →
      2 * Nat.card X ∣ Nat.card (Subgroup.centralizer {u}) := by
  intro u hu hu2 hu1
  rw [hX, show (2 : ℕ) * 2 ^ 26 = 2 ^ 27 by norm_num]
  exact inner_involution_centralizer_two_pow hu hu2 hu1

end CFSG.Monster.B.GSide

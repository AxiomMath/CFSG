module

public import CFSG.Monster.B.GSide.HInnerFusionCert
public import CFSG.Monster.B.CTIB.HInner
public import CFSG.Monster.B.CTIB.TableSixLength
public import CFSG.Monster.B.GSide.Setup
public import CFSG.Monster.B.GSide.FusionBasic
public import CFSG.Monster.B.CTIB.HOuterCert
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
public import Certificates.Certificate3122
public import Certificates.Certificate3123
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

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam
open CFSG.Monster.B.CTIB.Native (qmul gArr liftImgsN sqCode autApply)
open CFSG.Sporadic.Co2Inv (co2_involution_input)
open scoped Pointwise

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem isPGroup_zpowers_of_pow_four {G : Type*} [Group G] {g : G} (h : g ^ 4 = 1) :
    IsPGroup 2 (Subgroup.zpowers g) := by
  have hd : orderOf g ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one h
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])

theorem exists_conj_mem_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (K : Subgroup G) (hK : ¬ p ∣ K.index) {P : Subgroup G}
    (hP : IsPGroup p P) : ∃ g : G, ∀ x ∈ P, g * x * g⁻¹ ∈ K := by
  obtain ⟨S₀⟩ : Nonempty (Sylow p K) := inferInstance
  set T : Subgroup G := (S₀ : Subgroup K).map K.subtype with hTdef
  have hT : IsPGroup p T := S₀.isPGroup'.map K.subtype
  have hTK : T ≤ K := Subgroup.map_subtype_le _
  have hsub : T.subgroupOf K = (S₀ : Subgroup K) :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hidx : T.index = (S₀ : Subgroup K).index * K.index := by
    rw [← Subgroup.relIndex_mul_index hTK, Subgroup.relIndex, hsub]
  have hTidx : ¬ p ∣ T.index := by
    rw [hidx]
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).1 h with h' | h'
    · exact S₀.not_dvd_index h'
    · exact hK h'
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (hT.toSylow hTidx)
  refine ⟨g, fun x hx => hTK ?_⟩
  have hmem : MulAut.conj g x ∈ MulAut.conj g • (Q : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q : Subgroup G) (hPQ hx)
  rw [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem conj_mul_conj' {G : Type*} [Group G] (g a b : G) :
    g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by
  group

theorem innerTyRank_eq_1860 {k : ℕ} (h : innerTyRank k = 1860) : k = 1 := by
  unfold innerTyRank at h
  rcases k with _ | _ | _ | _ | _ | _ | _ | k <;> simp_all

theorem qS_mem_Qs_of_mem_jClass {u : Sbp} (h : u ∈ jClass (qS 1)) : u ∈ Qs := by
  obtain ⟨g, hg, rfl⟩ := h
  exact conj_mem_Qs hg (qS_mem 1)

theorem mul_self_of_mem_jClass
    {u : Sbp} (h : u ∈ jClass (qS 1)) : u * u = 1 := by
  obtain ⟨g, -, rfl⟩ := h
  calc g⁻¹ * qS 1 * g * (g⁻¹ * qS 1 * g) = g⁻¹ * (qS 1 * qS 1) * g := by group
    _ = 1 := by rw [qS_one_mul_self]; group

theorem rank_of_mem_jClass
    {u : Sbp} (h : u ∈ jClass (qS 1)) : ((βr u) - 1).rank = 1860 := by
  rw [rank_beta_conj (isConj_of_mem_jClass h), rank_qS_one]

theorem innerTy_eq_one_of_mem
    {n : ℕ} (hn : n < 2 ^ 23) (h : qS n ∈ jClass (qS 1)) :
    innerTy innerTab n = 1 := by
  obtain ⟨-, h1, h2⟩ := innerRank_spec hn
  have hsq := mul_self_of_mem_jClass h
  have hne : innerTyRank (innerTy innerTab n) ≠ 1 := fun e =>
    xs_ne_one' ((h1 e).symm.trans hsq)
  have hr := (h2 hne).2
  rw [rank_of_mem_jClass h] at hr
  exact innerTyRank_eq_1860 hr.symm

theorem mem_jClass_of_innerTy
    {n : ℕ} (hn : n < 2 ^ 23) (h : innerTy innerTab n = 1) :
    qS n ∈ jClass (qS 1) := by
  rcases innerTy_spec hn with ⟨-, ht⟩ | ⟨-, ht⟩ | ⟨k, hk, ht, hmem⟩
  · rw [ht] at h
    exact absurd h (by decide)
  · rw [ht] at h
    exact absurd h (by decide)
  · have hk0 : k = 0 := by omega
    subst hk0
    exact mem_jClass_of (by decide) (qS_mem n) hmem

theorem rank_of_innerTy
    {n k : ℕ} (hn : n < 2 ^ 23) (h : innerTy innerTab n = k)
    (hk : innerTyRank k ≠ 1) : qS n * qS n = 1 ∧ ((βr (qS n)) - 1).rank = innerTyRank k := by
  obtain ⟨-, -, h2⟩ := innerRank_spec hn
  rw [h] at h2
  exact h2 hk

theorem cosetSqOK_parts
    {k : ℕ} (hk : IsRank k) {n : ℕ} (hn : n < 2 ^ 23) :
    innerTy innerTab (qmul gArr (sqCode k)
      (qmul gArr (autApply gArr (liftImgsK k).toArray n) n)) ≠ 1 := by
  have h := cosetSqOK_eq_true
  simp only [cosetSqOK, List.all_eq_true, Nat.all_eq_finRange_all, List.mem_finRange,
    bne_iff_ne, ne_eq, true_implies] at h
  have hk' : k ∈ [6, 8, 10] := by rcases hk with rfl | rfl | rfl <;> simp
  exact h k hk' ⟨n, hn⟩

theorem coset_sq_not_mem
    {k : ℕ} (hk : IsRank k) {n : ℕ} (hn : n < 2 ^ 23) :
    cosetElt k n * cosetElt k n ∉ jClass (qS 1) := by
  rw [cosetElt_sq hk]
  intro h
  exact cosetSqOK_parts hk hn (innerTy_eq_one_of_mem (qmul_lt _ _) h)

theorem exists_conj_cosetElt
    {s : Sbp} (hsJ : s.unop ∈ Jbar) (hsQ : s ∉ Qs)
    (hsq : s * s ∈ Qs) :
    ∃ k, IsRank k ∧ ∃ g : Sbp, g.unop ∈ Jbar ∧ ∃ n < 2 ^ 23, g * s * g⁻¹ = cosetElt k n := by
  set kt := piH ⟨s, hsJ⟩ with hkt
  have hk2 : kt * kt = 1 := by
    rw [hkt, ← map_mul, piH_eq_one_iff]
    exact hsq
  have hk1 : kt ≠ 1 := fun h => hsQ ((piH_eq_one_iff _).1 h)
  have main : ∀ r, IsRank r → rkW kt = r →
      ∃ k, IsRank k ∧ ∃ g : Sbp, g.unop ∈ Jbar ∧ ∃ n < 2 ^ 23, g * s * g⁻¹ = cosetElt k n := by
    intro r hr hrk
    have hc := kv_conj_of_rank co2_involution_input hk2 hk1 (piH_hs_sq hr) (piH_hs_ne_one hr)
      (by rw [hrk, rkW_hs hr])
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    obtain ⟨g, rfl⟩ := piH_surjective c
    set u : Sbp := g.val * s * g.val⁻¹ with hu
    have huJ : u.unop ∈ Jbar :=
      Jbar.op.mul_mem (Jbar.op.mul_mem g.2 hsJ) (Jbar.op.inv_mem g.2)
    have hpu : piH ⟨u, huJ⟩ = piH ⟨hs r, hs_mem_Jbar hr⟩ := by
      rw [← hc, hkt, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hq' : (hs r)⁻¹ * u ∈ Qs := by
      have h1 : piH (⟨hs r, hs_mem_Jbar hr⟩⁻¹ * ⟨u, huJ⟩) = 1 := by
        rw [map_mul, hpu, ← map_mul, inv_mul_cancel, map_one]
      exact (piH_eq_one_iff _).1 h1
    obtain ⟨n, hn, hqn⟩ := exists_qS hq'
    refine ⟨r, hr, g.val, g.2, n, hn, ?_⟩
    rw [cosetElt, hqn, ← hu]
    group
  rcases kv_rank_cases co2_involution_input hk2 hk1 with h | h | h
  · exact main 6 (.inl rfl) h
  · exact main 8 (.inr (.inl rfl)) h
  · exact main 10 (.inr (.inr rfl)) h

theorem one_not_mem_jClass :
    (1 : Sbp) ∉ jClass (qS 1) := fun h => by
  have := rank_of_mem_jClass h
  rw [rank_beta_one] at this
  exact absurd this (by decide)

theorem xs_not_mem_jClass :
    xs ∉ jClass (qS 1) := fun h => by
  have := rank_of_mem_jClass h
  rw [rank_xs] at this
  exact absurd this (by decide)

theorem sq_not_mem_jClass_of_Jbar
    {s : Sbp} (hsJ : s.unop ∈ Jbar) : s * s ∉ jClass (qS 1) := by
  intro h
  by_cases hsQ : s ∈ Qs
  · rcases sq_mem hsQ with e | e
    · exact one_not_mem_jClass (e ▸ h)
    · exact xs_not_mem_jClass (e ▸ h)
  · obtain ⟨k, hk, g, hg, n, hn, e⟩ :=
      exists_conj_cosetElt hsJ hsQ (qS_mem_Qs_of_mem_jClass h)
    apply coset_sq_not_mem hk hn
    rw [← e, conj_mul_conj']
    exact conj_mem_jClass hg h

theorem natCard_centralizer_qS_one :
    Nat.card (Subgroup.centralizer ({qS 1} : Set Sbp)) = 306129918735099415756800 := by
  obtain ⟨e⟩ := centralizer_equiv_Eam (centralizerInput_of_ambient ambientRootOrbitsHyp)
    isConj_qS_one_labelS
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨hidx, -, -, -, -, -, -, hcard⟩ := derivedCoverInput_holds
  rw [← Subgroup.card_mul_index (commutator Eam), hidx, hcard]

theorem natCard_centralizer_qS_one_xs :
    Nat.card ↥(Subgroup.centralizer ({qS 1} : Set Sbp) ⊓ Subgroup.centralizer {xs}) =
      77148607752437760 :=
  native_inner_involution_representatives.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem index_centralizer_qS_one_xs :
    ((Subgroup.centralizer ({qS 1} : Set Sbp) ⊓ Subgroup.centralizer {xs}).subgroupOf
      (Subgroup.centralizer {qS 1})).index = 3968055 := by
  have h1 := Subgroup.card_mul_index ((Subgroup.centralizer ({qS 1} : Set Sbp) ⊓
    Subgroup.centralizer {xs}).subgroupOf (Subgroup.centralizer {qS 1}))
  rw [natCard_centralizer_qS_one,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
    natCard_centralizer_qS_one_xs] at h1
  omega

theorem exists_conj_into_Jbar
    {s : Sbp} (hs1 : s * qS 1 = qS 1 * s) (hs4 : s ^ 4 = 1) :
    ∃ h : Sbp, h * qS 1 = qS 1 * h ∧ (h * s * h⁻¹).unop ∈ Jbar := by
  have hsC : s ∈ Subgroup.centralizer ({qS 1} : Set Sbp) :=
    Subgroup.mem_centralizer_singleton_iff.2 hs1
  have hP := isPGroup_zpowers_of_pow_four
    (g := (⟨s, hsC⟩ : Subgroup.centralizer ({qS 1} : Set Sbp)))
    (Subtype.ext (by simpa using hs4))
  have hidx : ¬ 2 ∣ ((Subgroup.centralizer ({qS 1} : Set Sbp) ⊓
      Subgroup.centralizer {xs}).subgroupOf (Subgroup.centralizer {qS 1})).index := by
    rw [index_centralizer_qS_one_xs]
    decide
  obtain ⟨g, hg⟩ := exists_conj_mem_of_not_dvd_index _ hidx hP
  have hmem := hg ⟨s, hsC⟩ (Subgroup.mem_zpowers _)
  rw [Subgroup.mem_subgroupOf] at hmem
  have h2 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hmem).2
  refine ⟨g, Subgroup.mem_centralizer_singleton_iff.1 g.2, ?_⟩
  rw [mem_Jbar_iff_comm]
  have h3 := congrArg MulOpposite.unop h2
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, unop_mul] at h3
  simpa [xs, mul_assoc] using h3

theorem no_square_of_isConj_labelS
    {s t : Sbp} (ht : IsConj t labelS) : s * s ≠ t := by
  intro hst
  obtain ⟨a, ha⟩ := isConj_iff.1 (ht.trans isConj_qS_one_labelS.symm)
  have hs₁ : a * s * a⁻¹ * (a * s * a⁻¹) = qS 1 := by rw [conj_mul_conj', hst, ha]
  have hc : a * s * a⁻¹ * qS 1 = qS 1 * (a * s * a⁻¹) := by
    rw [← hs₁, ← mul_assoc]
  have h4 : (a * s * a⁻¹) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hs₁, qS_one_mul_self]
  obtain ⟨h, hh, hJ⟩ := exists_conj_into_Jbar hc h4
  apply sq_not_mem_jClass_of_Jbar hJ
  rw [conj_mul_conj', hs₁, show h * qS 1 * h⁻¹ = qS 1 by rw [hh]; group]
  exact mem_jClass_self _

theorem labelS_mul_self :
    labelS * labelS = 1 := mul_self_of_mem_jClass labelS_mem_jClass

theorem rank_labelS :
    ((βr labelS) - 1).rank = 1860 := rank_of_mem_jClass labelS_mem_jClass

theorem mul_self_of_isConj_labelS
    {c : Sbp} (hc : IsConj c labelS) : c * c = 1 := by
  obtain ⟨a, ha⟩ := isConj_iff.1 hc
  have e : c = a⁻¹ * labelS * a := by rw [← ha]; group
  rw [e, show a⁻¹ * labelS * a * (a⁻¹ * labelS * a) = a⁻¹ * (labelS * labelS) * a by group,
    labelS_mul_self]
  group

theorem rank_of_isConj_labelS
    {c : Sbp} (hc : IsConj c labelS) : ((βr c) - 1).rank = 1860 := by
  rw [rank_beta_conj hc, rank_labelS]

theorem isConj_xs_of_rank
    {w : Sbp} (hw2 : w * w = 1) (hwr : ((βr w) - 1).rank = 2048) :
    IsConj w xs := by
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [rank_beta_one] at hwr
    exact absurd hwr (by decide)
  have hord : orderOf w = 2 := orderOf_eq_prime (by rw [sq, hw2]) hw1
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := four_classes co2_involution_input hord
  have e := rank_beta_conj hc
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · omega
  · rwa [rs0_eq] at hc
  · omega
  · omega

theorem centralizer_xs_comm
    {u : Sbp} (h : u * xs = xs * u) : u.unop ∈ Jbar := by
  rw [mem_Jbar_iff_comm]
  have h3 := congrArg MulOpposite.unop h
  rw [unop_mul, unop_mul] at h3
  exact h3

theorem rs_rank_eq_1860 {i : ℕ} (hi : i ∈ Finset.Icc 4 13)
    (h : Native.repRanks.getD i 0 = 1860) : i = 6 := by
  simp only [Finset.mem_Icc] at hi
  obtain ⟨h4, h13⟩ := hi
  interval_cases i <;> simp_all [Native.repRanks]

theorem qS_one_mul_xs_mem :
    qS 1 * xs ∈ jClass (qS 1) := by
  refine mem_jClass_of (by decide) (Qs.mul_mem (qS_mem 1) xs_mem) ?_
  rw [psiS_mul (qS_mem 1) xs_mem, psiS_xs, add_zero]
  exact mem_jOrbit_self _

theorem frame_two_B
    {c w : Sbp} (hc : IsConj c labelS) (hw2 : w * w = 1)
    (hwr : ((βr w) - 1).rank = 2048) (hcw : w * c = c * w) :
    (((βr (c * w)) - 1).rank = 1860 ∧ ∃ g : Sbp, g * c * g⁻¹ = qS 1 ∧ g * w * g⁻¹ = xs) ∨
      ∃ g : Sbp, g * c * g⁻¹ = rs 6 ∧ g * w * g⁻¹ = xs := by
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 (isConj_xs_of_rank hw2 hwr)
  have hc₁x : g₀ * c * g₀⁻¹ * xs = xs * (g₀ * c * g₀⁻¹) := by
    rw [← hg₀, conj_mul_conj', conj_mul_conj', hcw]
  have hc₁J := centralizer_xs_comm hc₁x
  have hc₁l : IsConj (g₀ * c * g₀⁻¹) labelS :=
    (isConj_iff.2 ⟨g₀⁻¹, by group⟩).trans hc
  have hc₁sq := mul_self_of_isConj_labelS hc₁l
  have hc₁r := rank_of_isConj_labelS hc₁l
  have hc₁ne : g₀ * c * g₀⁻¹ ≠ 1 := by
    intro e
    rw [e, rank_beta_one] at hc₁r
    exact absurd hc₁r (by decide)
  have hcw' : c * w = g₀⁻¹ * (g₀ * c * g₀⁻¹ * xs) * g₀ := by rw [← hg₀]; group
  by_cases hQ : g₀ * c * g₀⁻¹ ∈ Qs
  · left
    have hmem : g₀ * c * g₀⁻¹ ∈ {t | t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1} := ⟨hQ, hc₁sq, hc₁ne⟩
    rw [invs_eq] at hmem
    have hj : g₀ * c * g₀⁻¹ ∈ jClass (qS 1) := by
      rcases hmem with ((h | h) | h) | h
      · have := rank_beta_conj (isConj_of_mem_jClass h)
        rw [hc₁r, rs0_eq, rank_xs] at this
        exact absurd this (by decide)
      · rwa [rs1_eq] at h
      · have := rank_beta_conj (isConj_of_mem_jClass h)
        rw [hc₁r, rank_rs (by norm_num : 2 < 14)] at this
        exact absurd this (by decide)
      · have := rank_beta_conj (isConj_of_mem_jClass h)
        rw [hc₁r, rank_rs (by norm_num : 3 < 14)] at this
        exact absurd this (by decide)
    obtain ⟨j, hj, hjc⟩ := hj
    have hjx : j * xs * j⁻¹ = xs := by
      have := conj_xs (g := j⁻¹) (Jbar.op.inv_mem hj)
      rwa [inv_inv] at this
    have hjx' : j * xs = xs * j := by
      calc j * xs = j * xs * j⁻¹ * j := by group
        _ = xs * j := by rw [hjx]
    refine ⟨?_, j * g₀, ?_, ?_⟩
    · rw [hcw', rank_conj]
      have h' := conj_mem_jClass (g := j⁻¹) (Jbar.op.inv_mem hj) qS_one_mul_xs_mem
      rw [inv_inv] at h'
      have e : g₀ * c * g₀⁻¹ * xs = j⁻¹ * (qS 1 * xs) * j := by
        rw [hjc]
        calc j⁻¹ * qS 1 * j * xs = j⁻¹ * qS 1 * (j * xs) := by group
          _ = j⁻¹ * qS 1 * (xs * j) := by rw [hjx']
          _ = j⁻¹ * (qS 1 * xs) * j := by group
      rw [e]
      exact rank_of_mem_jClass h'
    · rw [show j * g₀ * c * (j * g₀)⁻¹ = j * (g₀ * c * g₀⁻¹) * j⁻¹ by group, hjc]
      group
    · rw [show j * g₀ * w * (j * g₀)⁻¹ = j * (g₀ * w * g₀⁻¹) * j⁻¹ by group, hg₀, hjx]
  · right
    obtain ⟨i, hi, hci⟩ := exists_jClass_rs hc₁J hc₁sq hQ
    have hi6 : i = 6 := by
      have := rank_beta_conj (isConj_of_mem_jClass hci)
      rw [hc₁r, rank_rs (by simp only [Finset.mem_Icc] at hi; omega)] at this
      exact rs_rank_eq_1860 hi this.symm
    subst hi6
    obtain ⟨j, hj, hjc⟩ := hci
    have hjx : j * xs * j⁻¹ = xs := by
      have := conj_xs (g := j⁻¹) (Jbar.op.inv_mem hj)
      rwa [inv_inv] at this
    refine ⟨j * g₀, ?_, ?_⟩
    · rw [show j * g₀ * c * (j * g₀)⁻¹ = j * (g₀ * c * g₀⁻¹) * j⁻¹ by group, hjc]
      group
    · rw [show j * g₀ * w * (j * g₀)⁻¹ = j * (g₀ * w * g₀⁻¹) * j⁻¹ by group, hg₀, hjx]

theorem fusionWitness_parts :
    innerTy innerTab 128 = 1 ∧ autApply gArr (liftImgsK 8).toArray 128 = 128 ∧
    qmul gArr 128 2 = qmul gArr 2 128 ∧ qmul gArr 128 35 = qmul gArr 35 128 ∧
    qmul gArr (sqCode 8) (qmul gArr (autApply gArr (liftImgsK 8).toArray 2) 2) = 1270988 ∧
    qmul gArr (sqCode 8) (qmul gArr (autApply gArr (liftImgsK 8).toArray 35) 35) = 1255411 ∧
    qmul gArr 1270988 128 = qmul gArr 128 1270988 ∧
    qmul gArr 1255411 128 = qmul gArr 128 1255411 ∧
    innerTy innerTab 1270988 = 2 ∧ innerTy innerTab (qmul gArr 128 1270988) = 3 ∧
    innerTy innerTab 1255411 = 3 ∧ innerTy innerTab (qmul gArr 128 1255411) = 2 ∧
    qmul gArr 34 1 = qmul gArr 1 34 ∧ qmul gArr 34 34 = 2 ^ 22 := by
  have h := fusionWitnessOK_eq_true
  simp only [fusionWitnessOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

theorem qS_comm_of_code
    {a b : ℕ} (h : qmul gArr a b = qmul gArr b a) :
    qS a * qS b = qS b * qS a := by
  rw [qS_mul, qS_mul, h]

theorem isConj_qS128_labelS :
    IsConj (qS 128) labelS :=
  (isConj_of_mem_jClass (mem_jClass_of_innerTy (by norm_num) fusionWitness_parts.1)).trans
    isConj_qS_one_labelS

theorem cosetElt8_comm
    {n : ℕ} (h : qmul gArr 128 n = qmul gArr n 128) :
    cosetElt 8 n * qS 128 = qS 128 * cosetElt 8 n := by
  have h8 : (hs 8)⁻¹ * qS 128 * hs 8 = qS 128 := by
    rw [conj_hs_qS (by decide : IsRank 8), fusionWitness_parts.2.1]
  have h8' : hs 8 * qS 128 = qS 128 * hs 8 := by
    calc hs 8 * qS 128 = hs 8 * ((hs 8)⁻¹ * qS 128 * hs 8) := by rw [h8]
      _ = qS 128 * hs 8 := by group
  rw [cosetElt, mul_assoc, qS_comm_of_code h.symm, ← mul_assoc, h8', mul_assoc]

theorem exists_sqrt_xs_rs6 :
    ∃ s : Sbp, s * rs 6 = rs 6 * s ∧ s * s = xs := by
  obtain ⟨-, -, h2, -, h4, -, h6, -, h8, h9, -⟩ := fusionWitness_parts
  obtain ⟨hy2, hyr⟩ := rank_of_innerTy (k := 2) (by norm_num) h8 (by decide)
  have hcy : qS 1270988 * qS 128 = qS 128 * qS 1270988 := qS_comm_of_code h6
  have hr3 : ((βr (qS 128 * qS 1270988)) - 1).rank = 2168 := by
    rw [qS_mul]
    exact (rank_of_innerTy (k := 3) (qmul_lt _ _) h9 (by decide)).2
  rcases frame_two_B isConj_qS128_labelS hy2 hyr hcy with ⟨hr1, -⟩ | ⟨g, hgc, hgw⟩
  · rw [hr3] at hr1
    exact absurd hr1 (by decide)
  · refine ⟨g * cosetElt 8 2 * g⁻¹, ?_, ?_⟩
    · rw [← hgc, conj_mul_conj', conj_mul_conj', cosetElt8_comm h2]
    · rw [conj_mul_conj', cosetElt_sq (by decide : IsRank 8), h4, hgw]

theorem exists_sqrt_rs6xs_rs6 :
    ∃ s : Sbp, s * rs 6 = rs 6 * s ∧ s * s = rs 6 * xs := by
  obtain ⟨-, -, -, h3, -, h5, -, h7, -, -, h10, h11, -⟩ := fusionWitness_parts
  obtain ⟨hy2, hyr⟩ := rank_of_innerTy (k := 3) (by norm_num) h10 (by decide)
  have hcy : qS 1255411 * qS 128 = qS 128 * qS 1255411 := qS_comm_of_code h7
  have h128 : qS 128 * qS 128 = 1 := mul_self_of_isConj_labelS isConj_qS128_labelS
  obtain ⟨hw2, hwr⟩ := rank_of_innerTy (k := 2) (qmul_lt _ _) h11 (by decide)
  rw [← qS_mul] at hw2 hwr
  have hcw : qS 128 * qS 1255411 * qS 128 = qS 128 * (qS 128 * qS 1255411) := by
    rw [mul_assoc, ← hcy]
  have hy : qS 128 * (qS 128 * qS 1255411) = qS 1255411 := by
    rw [← mul_assoc, h128, one_mul]
  rcases frame_two_B isConj_qS128_labelS hw2 hwr hcw with ⟨hr1, -⟩ | ⟨g, hgc, hgw⟩
  · rw [hy, hyr] at hr1
    exact absurd hr1 (by decide)
  · refine ⟨g * cosetElt 8 35 * g⁻¹, ?_, ?_⟩
    · rw [← hgc, conj_mul_conj', conj_mul_conj', cosetElt8_comm h3]
    · rw [conj_mul_conj', cosetElt_sq (by decide : IsRank 8), h5, ← hy, ← conj_mul_conj', hgc,
        hgw]

theorem exists_sqrt_xs_qS_one :
    ∃ s : Sbp, s * qS 1 = qS 1 * s ∧ s * s = xs := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, h14⟩ := fusionWitness_parts
  exact ⟨qS 34, qS_comm_of_code h13, by rw [qS_mul, h14, qS_two_pow_22]⟩

theorem sqrt_conj {c c₀ y y₀ g s : Sbp} (hgc : g * c * g⁻¹ = c₀) (hgy : g * y * g⁻¹ = y₀)
    (hs : s * c₀ = c₀ * s) (hs2 : s * s = y₀) :
    g⁻¹ * s * g * c = c * (g⁻¹ * s * g) ∧ g⁻¹ * s * g * (g⁻¹ * s * g) = y := by
  have ec : c = g⁻¹ * c₀ * g := by rw [← hgc]; group
  have ey : y = g⁻¹ * y₀ * g := by rw [← hgy]; group
  refine ⟨?_, ?_⟩
  · rw [ec, conj_mul_conj, conj_mul_conj, hs]
  · rw [conj_mul_conj, hs2, ey]

theorem square_of_rank_2048
    {c y : Sbp} (hc : IsConj c labelS) (hy2 : y * y = 1)
    (hyr : ((βr y) - 1).rank = 2048) (hcy : y * c = c * y) :
    ∃ s : Sbp, s * c = c * s ∧ s * s = y := by
  rcases frame_two_B hc hy2 hyr hcy with ⟨-, g, hgc, hgy⟩ | ⟨g, hgc, hgy⟩
  · obtain ⟨s₀, hs₀c, hs₀⟩ := exists_sqrt_xs_qS_one
    exact ⟨_, sqrt_conj hgc hgy hs₀c hs₀⟩
  · obtain ⟨s₀, hs₀c, hs₀⟩ := exists_sqrt_xs_rs6
    exact ⟨_, sqrt_conj hgc hgy hs₀c hs₀⟩

theorem square_of_rank_mul_2048
    {c y : Sbp} (hc : IsConj c labelS) (hy2 : y * y = 1)
    (hcy : y * c = c * y) (hr : ((βr (c * y)) - 1).rank = 2048)
    (hr' : ((βr y) - 1).rank ≠ 1860) : ∃ s : Sbp, s * c = c * s ∧ s * s = y := by
  have hcc := mul_self_of_isConj_labelS hc
  have hw2 : c * y * (c * y) = 1 := by
    calc c * y * (c * y) = c * (y * c) * y := by group
      _ = c * (c * y) * y := by rw [hcy]
      _ = 1 := by rw [← mul_assoc, hcc, one_mul, hy2]
  have hcw : c * y * c = c * (c * y) := by rw [mul_assoc, hcy]
  have hcy' : c * (c * y) = y := by rw [← mul_assoc, hcc, one_mul]
  rcases frame_two_B hc hw2 hr hcw with ⟨hr1, -⟩ | ⟨g, hgc, hgw⟩
  · rw [hcy'] at hr1
    exact absurd hr1 hr'
  · obtain ⟨s₀, hs₀c, hs₀⟩ := exists_sqrt_rs6xs_rs6
    have hgy : g * y * g⁻¹ = rs 6 * xs := by
      rw [← hcy', ← hgc, ← hgw, conj_mul_conj']
    exact ⟨_, sqrt_conj hgc hgy hs₀c hs₀⟩

theorem map_conj_inf_centralizer (g a b : Sbp) :
    (Subgroup.centralizer ({a} : Set Sbp) ⊓ Subgroup.centralizer {b}).map
      (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer {g * a * g⁻¹} ⊓ Subgroup.centralizer {g * b * g⁻¹} := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨u, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [conj_mul_conj', conj_mul_conj', h1]
    · rw [conj_mul_conj', conj_mul_conj', h2]
  · rintro ⟨h1, h2⟩
    refine ⟨g⁻¹ * z * g, ⟨?_, ?_⟩, by group⟩
    · calc g⁻¹ * z * g * a = g⁻¹ * (z * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * a * g⁻¹ * z) * g := by rw [h1]
        _ = a * (g⁻¹ * z * g) := by group
    · calc g⁻¹ * z * g * b = g⁻¹ * (z * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * b * g⁻¹ * z) * g := by rw [h2]
        _ = b * (g⁻¹ * z * g) := by group

theorem natCard_inf_centralizer_conj
    (g a b : Sbp) :
    Nat.card ↥(Subgroup.centralizer ({g * a * g⁻¹} : Set Sbp) ⊓
      Subgroup.centralizer {g * b * g⁻¹}) =
      Nat.card ↥(Subgroup.centralizer ({a} : Set Sbp) ⊓ Subgroup.centralizer {b}) := by
  rw [← map_conj_inf_centralizer, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem centralizer_xs_eq :
    Subgroup.centralizer ({xs} : Set Sbp) = Jbar.op := by
  ext u
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_op]
  constructor
  · exact centralizer_xs_comm
  · intro h
    have h' := mem_Jbar_iff_comm.1 h
    apply MulOpposite.unop_injective
    rw [unop_mul, unop_mul]
    exact h'

theorem natCard_Jbar_op :
    Nat.card Jbar.op = 2 ^ 41 * 161382375 := by
  rw [← Nat.card_congr (Subgroup.equivOp Jbar), natCard_Jbar_eq]

theorem rs6_mem_Jbar_op :
    rs 6 ∈ Jbar.op :=
  (native_table_six.2.2.2.1 6 6 64 64 1860 1 (by decide)).1

theorem natCard_centralizer_rs6_xs :
    Nat.card ↥(Subgroup.centralizer ({rs 6} : Set Sbp) ⊓ Subgroup.centralizer {xs}) =
      97409858273280 := by
  set J : Subgroup Sbp := Jbar.op with hJ
  set r : J := ⟨rs 6, rs6_mem_Jbar_op⟩ with hr
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct J) r)
  rw [MulAction.index_stabilizer, ← Subgroup.nat_card_centralizer_nat_card_stabilizer] at h1
  have horb : (MulAction.orbit (ConjAct J) r).ncard = (jClass (rs 6)).ncard := by
    have e : Subtype.val '' MulAction.orbit (ConjAct J) r = jClass (rs 6) := by
      ext u
      simp only [Set.mem_image, ConjAct.mem_orbit_conjAct]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨c, hc⟩ := isConj_iff.1 hy.symm
        refine ⟨(c : Sbp)⁻¹, J.inv_mem c.2, ?_⟩
        rw [← hc]
        simp [hr]
      · rintro ⟨g, hg, rfl⟩
        refine ⟨⟨g⁻¹ * rs 6 * g, J.mul_mem (J.mul_mem (J.inv_mem hg) rs6_mem_Jbar_op) hg⟩,
          ?_, rfl⟩
        exact (isConj_iff.2 ⟨⟨g, hg⟩⁻¹, Subtype.ext (by simp [hr])⟩).symm
    rw [← e, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hcent : Nat.card (Subgroup.centralizer ({r} : Set J)) =
      Nat.card ↥(Subgroup.centralizer ({rs 6} : Set Sbp) ⊓ Subgroup.centralizer {xs}) := by
    have e : (Subgroup.centralizer ({r} : Set J)).map J.subtype =
        Subgroup.centralizer ({rs 6} : Set Sbp) ⊓ Subgroup.centralizer {xs} := by
      ext u
      simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.coe_subtype]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨?_, ?_⟩
        · have := congrArg Subtype.val hy
          simpa [hr] using this
        · have hy2 : (y : Sbp) ∈ Subgroup.centralizer ({xs} : Set Sbp) := by
            rw [centralizer_xs_eq]
            exact y.2
          exact Subgroup.mem_centralizer_singleton_iff.1 hy2
      · rintro ⟨h1, h2⟩
        have hu : u ∈ J := by
          rw [hJ, ← centralizer_xs_eq]
          exact Subgroup.mem_centralizer_singleton_iff.2 h2
        exact ⟨⟨u, hu⟩, Subtype.ext (by simpa [hr] using h1), rfl⟩
    rw [← e, Subgroup.card_map_of_injective J.subtype_injective]
  rw [hcent, horb, ncard_jClass_rs_six (i := 6) (n := 64) (m := 64) (ρ := 1860) (b := 1)
      (by decide),
    Nat.card_congr ConjAct.toConjAct.symm.toEquiv, natCard_Jbar_op] at h1
  have e : (2 : ℕ) ^ 41 * 161382375 = 97409858273280 * (56925 * 64) := by norm_num
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h1.trans e)

theorem frame_two_B_card
    {c w : Sbp} (hc : IsConj c labelS) (hw2 : w * w = 1)
    (hwr : ((βr w) - 1).rank = 2048) (hcw : w * c = c * w) :
    (((βr (c * w)) - 1).rank = 1860 ∧
        Nat.card ↥(Subgroup.centralizer ({c} : Set Sbp) ⊓ Subgroup.centralizer {w}) =
          77148607752437760) ∨
      (((βr (c * w)) - 1).rank = 2168 ∧
        Nat.card ↥(Subgroup.centralizer ({c} : Set Sbp) ⊓ Subgroup.centralizer {w}) =
          97409858273280) := by
  rcases frame_two_B hc hw2 hwr hcw with ⟨hr, g, hgc, hgw⟩ | ⟨g, hgc, hgw⟩
  · refine .inl ⟨hr, ?_⟩
    rw [← natCard_inf_centralizer_conj g, hgc, hgw, natCard_centralizer_qS_one_xs]
  · refine .inr ⟨?_, ?_⟩
    · have e : c * w = g⁻¹ * (rs 6 * xs) * g := by rw [← hgc, ← hgw]; group
      rw [e, rank_conj, rank_rs6_mul_xs]
    · rw [← natCard_inf_centralizer_conj g, hgc, hgw, natCard_centralizer_rs6_xs]

theorem sEquiv_labelS_eq_cV0 :
    sEquiv labelS = (cV0 : Shat) := by
  rw [sEquiv_labelS, cS_inv, coe_cV0, clabelS_cv0]

theorem sEquiv_symm_cV0 :
    sEquiv.symm (cV0 : Shat) = labelS := by
  rw [← sEquiv_labelS_eq_cV0, MulEquiv.symm_apply_apply]

theorem commute_labelS_iff_mem
    (s : Sbp) :
    s * labelS = labelS * s ↔ sEquiv s ∈ vStab cv0 := by
  rw [commute_iff_sEquiv, sEquiv_labelS_eq_cV0, coe_cV0, coe_clabelS]
  exact (centralizerInput_of_ambient ambientRootOrbitsHyp) cv0 (sEquiv s)

theorem commute_labelS_of_mem
    (y : vStab cv0) :
    sEquiv.symm (y : Shat) * labelS = labelS * sEquiv.symm (y : Shat) := by
  rw [commute_labelS_iff_mem, MulEquiv.apply_symm_apply]
  exact y.2

@[expose] def rkH
    (y : vStab cv0) : ℕ := ((βr (sEquiv.symm (y : Shat))) - 1).rank

theorem rkH_cV0_mul
    (y : vStab cv0) :
    rkH (cV0 * y) = ((βr (labelS * sEquiv.symm (y : Shat))) - 1).rank := by
  rw [rkH, Subgroup.coe_mul, map_mul, sEquiv_symm_cV0]

theorem rkH_cV0 :
    rkH cV0 = 1860 := by
  rw [rkH, sEquiv_symm_cV0, rank_labelS]

theorem mul_self_symm
    {y : vStab cv0} (h : y * y = 1) :
    sEquiv.symm (y : Shat) * sEquiv.symm (y : Shat) = 1 := by
  rw [← map_mul, ← Subgroup.coe_mul, h, Subgroup.coe_one, map_one]

theorem no_square_cV0
    (s : vStab cv0) : s * s ≠ cV0 := by
  intro h
  apply no_square_of_isConj_labelS (s := sEquiv.symm (s : Shat)) (IsConj.refl labelS)
  rw [← map_mul, ← Subgroup.coe_mul, h, sEquiv_symm_cV0]

theorem square_of_S
    {y : vStab cv0} {s : Sbp} (hs : s * labelS = labelS * s)
    (hs2 : s * s = sEquiv.symm (y : Shat)) : ∃ t : vStab cv0, t * t = y := by
  refine ⟨⟨sEquiv s, (commute_labelS_iff_mem s).1 hs⟩, Subtype.ext ?_⟩
  show sEquiv s * sEquiv s = (y : Shat)
  rw [← map_mul, hs2, MulEquiv.apply_symm_apply]

theorem square_of_rkH_2048
    {y : vStab cv0} (hy2 : y * y = 1) (hr : rkH y = 2048) :
    ∃ s : vStab cv0, s * s = y := by
  obtain ⟨s, hsc, hs2⟩ := square_of_rank_2048 (IsConj.refl labelS) (mul_self_symm hy2) hr
    (commute_labelS_of_mem y)
  exact square_of_S hsc hs2

theorem square_of_rkH_mul_2048
    {y : vStab cv0} (hy2 : y * y = 1) (hr : rkH (cV0 * y) = 2048)
    (hr' : rkH y ≠ 1860) : ∃ s : vStab cv0, s * s = y := by
  rw [rkH_cV0_mul] at hr
  obtain ⟨s, hsc, hs2⟩ := square_of_rank_mul_2048 (IsConj.refl labelS) (mul_self_symm hy2)
    (commute_labelS_of_mem y) hr hr'
  exact square_of_S hsc hs2

theorem natCard_centralizer_vStab
    (y : vStab cv0) :
    Nat.card (Subgroup.centralizer ({y} : Set (vStab cv0))) =
      Nat.card ↥(Subgroup.centralizer ({labelS} : Set Sbp) ⊓
        Subgroup.centralizer {sEquiv.symm (y : Shat)}) := by
  set Φ : vStab cv0 →* Sbp := sEquiv.symm.toMonoidHom.comp (vStab cv0).subtype with hΦ
  have hinj : Function.Injective Φ :=
    sEquiv.symm.injective.comp (vStab cv0).subtype_injective
  have e : (Subgroup.centralizer ({y} : Set (vStab cv0))).map Φ =
      Subgroup.centralizer ({labelS} : Set Sbp) ⊓
        Subgroup.centralizer {sEquiv.symm (y : Shat)} := by
    ext u
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, hΦ,
      MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, Function.comp_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨commute_labelS_of_mem z, ?_⟩
      rw [← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hz]
    · rintro ⟨h1, h2⟩
      refine ⟨⟨sEquiv u, (commute_labelS_iff_mem u).1 h1⟩, Subtype.ext ?_, ?_⟩
      · show sEquiv u * (y : Shat) = (y : Shat) * sEquiv u
        apply sEquiv.symm.injective
        rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
        exact h2
      · exact MulEquiv.symm_apply_apply _ _
  rw [← e, Subgroup.card_map_of_injective hinj]

theorem natCard_centralizer_of_rkH_2048
    {y : vStab cv0} (hy2 : y * y = 1)
    (hr : rkH y = 2048) :
    (rkH (cV0 * y) = 1860 ∧ Nat.card (Subgroup.centralizer ({y} : Set (vStab cv0))) =
        77148607752437760) ∨
      (rkH (cV0 * y) = 2168 ∧ Nat.card (Subgroup.centralizer ({y} : Set (vStab cv0))) =
        97409858273280) := by
  rw [rkH_cV0_mul, natCard_centralizer_vStab]
  exact frame_two_B_card (IsConj.refl labelS) (mul_self_symm hy2) hr
    (commute_labelS_of_mem y)

theorem not_mem_dH_of_square
    {G : Type*} [Group G] {d : G}
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) {y s : vStab cv0} (hs : s * s = y)
    (hne : y ≠ cV0) : y ∉ dH ψ := by
  intro hy
  obtain ⟨y', -, -, θ, -, hθy, -, -⟩ := exists_swap_cV0 ψ hψ hy hne
  have hsC : s ∈ Subgroup.centralizer ({y} : Set (vStab cv0)) :=
    Subgroup.mem_centralizer_singleton_iff.2 (by rw [← hs, mul_assoc])
  have ht : (⟨s, hsC⟩ : Subgroup.centralizer ({y} : Set (vStab cv0))) * ⟨s, hsC⟩ =
      ⟨y, mem_centralizer_singleton_self y⟩ := Subtype.ext hs
  have h2 := congrArg (fun z => ((θ z : Subgroup.centralizer ({y'} : Set (vStab cv0))) :
    vStab cv0)) ht
  simp only [map_mul, Subgroup.coe_mul] at h2
  exact no_square_cV0 _ (h2.trans hθy)

theorem ne_cV0_of_rkH
    {y : vStab cv0} (h : rkH y ≠ 1860) : y ≠ cV0 := by
  rintro rfl
  exact h rkH_cV0

theorem not_mem_dH_of_rkH_2048
    {G : Type*} [Group G] {d : G}
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) {y : vStab cv0} (hy2 : y * y = 1)
    (hr : rkH y = 2048) : y ∉ dH ψ := by
  obtain ⟨s, hs⟩ := square_of_rkH_2048 hy2 hr
  exact not_mem_dH_of_square ψ hψ hs (ne_cV0_of_rkH (by rw [hr]; decide))

theorem not_mem_dH_of_rkH_mul_2048
    {G : Type*} [Group G] {d : G}
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) {y : vStab cv0} (hy2 : y * y = 1)
    (hr : rkH (cV0 * y) = 2048) (hr' : rkH y ≠ 1860) : y ∉ dH ψ := by
  obtain ⟨s, hs⟩ := square_of_rkH_mul_2048 hy2 hr hr'
  exact not_mem_dH_of_square ψ hψ hs (ne_cV0_of_rkH hr')

theorem native_inner_square_fusion :
    (∀ s t : Sbp, IsConj t labelS → s * s ≠ t) ∧
    (∀ s : vStab cv0, s * s ≠ cV0) ∧
    (∀ y : vStab cv0, y * y = 1 → rkH y = 2048 → ∃ s : vStab cv0, s * s = y) ∧
    (∀ y : vStab cv0, y * y = 1 → rkH (cV0 * y) = 2048 → rkH y ≠ 1860 →
      ∃ s : vStab cv0, s * s = y) ∧
    (∀ y : vStab cv0, y * y = 1 → rkH y = 2048 →
      (rkH (cV0 * y) = 1860 ∧ Nat.card (Subgroup.centralizer ({y} : Set (vStab cv0))) =
          77148607752437760) ∨
        (rkH (cV0 * y) = 2168 ∧ Nat.card (Subgroup.centralizer ({y} : Set (vStab cv0))) =
          97409858273280)) ∧
    (∀ (G : Type) [Group G] (d : G) (ψ : Subgroup.centralizer {d} ≃* vStab cv0),
      ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0 → ∀ y : vStab cv0, y * y = 1 →
        (rkH y = 2048 ∨ (rkH (cV0 * y) = 2048 ∧ rkH y ≠ 1860)) → y ∉ dH ψ) :=
  ⟨fun _ _ ht => no_square_of_isConj_labelS ht, no_square_cV0,
    fun _ hy2 hr => square_of_rkH_2048 hy2 hr,
    fun _ hy2 hr hr' => square_of_rkH_mul_2048 hy2 hr hr',
    fun _ hy2 hr => natCard_centralizer_of_rkH_2048 hy2 hr,
    fun _ _ _ ψ hψ _ hy2 h => h.elim (fun hr => not_mem_dH_of_rkH_2048 ψ hψ hy2 hr)
      (fun hr => not_mem_dH_of_rkH_mul_2048 ψ hψ hy2 hr.1 hr.2)⟩

end CFSG.Monster.B.GSide

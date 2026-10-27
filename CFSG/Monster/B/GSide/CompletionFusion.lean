module

public import CFSG.Monster.B.GSide.CompletionSubgroup
public import CFSG.Monster.B.GSide.FusionBasic
public import CFSG.Monster.B.GSide.HInnerFusion
public import CFSG.Monster.B.CTIB.DistThreeProductFinal
public import CFSG.Monster.B.CTIB.Rank2158
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentFinal
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

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.CTIB
open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def rankS
    (s : Shat) : ℕ := ((βr (sEquiv.symm s)) - 1).rank

theorem isConj_sEquiv_symm_iff {s s' : Shat} :
    IsConj (sEquiv.symm s) (sEquiv.symm s') ↔ IsConj s s' := by
  constructor
  · intro h
    have h' := sEquiv.toMonoidHom.map_isConj h
    simpa using h'
  · exact sEquiv.symm.toMonoidHom.map_isConj

theorem rankS_conj
    {s s' : Shat} (h : IsConj s s') : rankS s = rankS s' :=
  rank_beta_conj (isConj_sEquiv_symm_iff.2 h)

theorem orderOf_sEquiv_symm (s : Shat) : orderOf (sEquiv.symm s) = orderOf s :=
  MulEquiv.orderOf_eq _ _

theorem rankS_mem_of_orderOf
    {s : Shat} (hs : orderOf s = 2) :
    rankS s = 1860 ∨ rankS s = 2048 ∨ rankS s = 2158 ∨ rankS s = 2168 := by
  have h4 := four_classes co2_involution_input ((orderOf_sEquiv_symm s).trans hs)
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := h4
  have e : rankS s = ((βr (rs i)) - 1).rank := rank_beta_conj hc
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> omega

theorem isConj_of_rankS_eq
    {s s' : Shat} (hs : orderOf s = 2) (hs' : orderOf s' = 2)
    (h : rankS s = rankS s') : IsConj s s' := by
  have h4 := four_classes co2_involution_input ((orderOf_sEquiv_symm s).trans hs)
  have h4' := four_classes co2_involution_input ((orderOf_sEquiv_symm s').trans hs')
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := h4
  obtain ⟨j, ⟨hj, hc'⟩, -⟩ := h4'
  have e : rankS s = ((βr (rs i)) - 1).rank := rank_beta_conj hc
  have e' : rankS s' = ((βr (rs j)) - 1).rank := rank_beta_conj hc'
  have hij : i = j := by
    obtain ⟨r1, r0, r5, r3⟩ := rank_four
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;> omega
  subst hij
  exact isConj_sEquiv_symm_iff.1 (hc.trans hc'.symm)

theorem orderOf_coe_cV0 :
    orderOf (cV0 : Shat) = 2 := by
  rw [Subgroup.orderOf_coe, orderOf_cV0]

theorem rankS_cV0 :
    rankS (cV0 : Shat) = 1860 := by
  have e : rankS (cV0 : Shat) = ((βr labelS) - 1).rank :=
    congrArg (fun x => ((βr x) - 1).rank) sEquiv_symm_cV0
  have e1 : ((βr (qS 1)) - 1).rank = 1860 := rs1_eq ▸ rank_four.1
  exact e.trans ((rank_beta_conj (isConj_of_mem_jClass labelS_mem_jClass)).trans e1)

theorem orderOf_sEquiv_xs : orderOf (sEquiv xs) = 2 := by
  rw [MulEquiv.orderOf_eq, orderOf_xs]

theorem rankS_sEquiv_xs :
    rankS (sEquiv xs) = 2048 :=
  (congrArg (fun x => ((βr x) - 1).rank) (sEquiv.symm_apply_apply xs)).trans rank_xs

theorem cV0_mul_clabelS_comm
    {u : CVert} (hu : u ∈ sphereDistThree cv0) :
    (cV0 : Shat) * clabelS u = clabelS u * cV0 := by
  have h := clabelS_mem_vStab_cv0_of_dist_three hu
  rw [← centralizer_cV0] at h
  exact (Subgroup.mem_centralizer_singleton_iff.1 h).symm

theorem cV0_mul_self_coe :
    (cV0 : Shat) * cV0 = 1 :=
  (orderOf_two_iff.1 orderOf_coe_cV0).1

theorem orderOf_cV0_mul_clabelS
    {u : CVert} (hu : u ∈ sphereDistThree cv0) :
    orderOf ((cV0 : Shat) * clabelS u) = 2 := by
  have hne : (cV0 : Shat) ≠ clabelS u := by
    intro h
    rw [coe_cV0] at h
    have h0 : clabel cv0 = clabel u := by
      have h1 := congrArg Subtype.val h
      rwa [coe_clabelS, coe_clabelS] at h1
    have h' := native_global_label_bijection_and_full_vertex_centralizer.1 h0
    rw [mem_sphereDistThree, ← h', SimpleGraph.dist_self] at hu
    exact absurd hu (by norm_num)
  have hll : clabelS u * clabelS u = 1 := (orderOf_two_iff.1 (orderOf_clabelS u)).1
  refine orderOf_two_iff.2 ⟨?_, fun h => hne ?_⟩
  · calc (cV0 : Shat) * clabelS u * (cV0 * clabelS u) =
          cV0 * (clabelS u * cV0) * clabelS u := by group
      _ = cV0 * cV0 * (clabelS u * clabelS u) := by rw [← cV0_mul_clabelS_comm hu]; group
      _ = 1 := by rw [cV0_mul_self_coe, hll, one_mul]
  · have h1 : (cV0 : Shat)⁻¹ = clabelS u := inv_eq_of_mul_eq_one_right h
    rw [← h1, inv_eq_of_mul_eq_one_right cV0_mul_self_coe]

theorem exists_rankS_clabelS_mul :
    ∃ u ∈ sphereDistThree cv0, rankS ((cV0 : Shat) * clabelS u) = 2158 := by
  obtain ⟨v, u, hvu, he⟩ := exists_witness_pair ambientRootOrbitsHyp
  obtain ⟨g, hg⟩ := cvMul_transitive v cv0
  refine ⟨cvMul u g, mem_sphereDistThree.2 ?_, ?_⟩
  · rw [← hg, dist_cvMul]
    exact hvu
  · have hc : IsConj (clabelS v * clabelS u) ((cV0 : Shat) * clabelS (cvMul u g)) := by
      rw [coe_cV0, ← hg, CFSG.Monster.B.GSide.clabelS_cvMul,
        CFSG.Monster.B.GSide.clabelS_cvMul]
      exact isConj_iff.2 ⟨g⁻¹, by group⟩
    have e1 : rankS (sEquiv (rs 6 * e2158)) = ((βr (rs 6 * e2158)) - 1).rank :=
      congrArg (fun x => ((βr x) - 1).rank) (sEquiv.symm_apply_apply _)
    rw [← rankS_conj hc, he, e1, rank_beta_conj isConj_rs6_mul_e2158]
    exact rank_four.2.2.1

variable {G : Type*} [Group G]

theorem not_isConj_of_two_pow_dvd
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0) {t : G}
    {K : Subgroup G} (hK : K ≤ Subgroup.centralizer {t}) (h : 2 ^ 39 ∣ Nat.card K) :
    ¬ IsConj d t := by
  intro hc
  obtain ⟨g, hg⟩ := isConj_iff.1 hc
  have hcard : Nat.card (Subgroup.centralizer {t}) = 306129918735099415756800 :=
    (Nat.card_congr (centralizerConjEquiv g hg).toEquiv).trans (natCard_centralizer_of_equiv ψ)
  have h' := h.trans (Subgroup.card_dvd_of_le hK)
  rw [hcard] at h'
  exact absurd h' (by norm_num)

theorem not_isConj_of_two_pow_dvd_inf
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (M : Subgroup G) {t : G} (h : 2 ^ 41 ∣ Nat.card (M ⊓ Subgroup.centralizer {t} : Subgroup G)) :
    ¬ IsConj d t :=
  not_isConj_of_two_pow_dvd ψ inf_le_right ((pow_dvd_pow 2 (by norm_num)).trans h)

theorem not_isConj_map_sEquiv_xs
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    {Φ : Shat →* G} (hΦ : Function.Injective Φ) : ¬ IsConj d (Φ (sEquiv xs)) := by
  have hN := native_sylow_two_center
  obtain ⟨-, ⟨T₀, hT₀c, -⟩, hall, -⟩ := hN
  have hK : (T₀ : Subgroup Sbp).map (Φ.comp sEquiv.toMonoidHom) ≤
      Subgroup.centralizer {Φ (sEquiv xs)} := by
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    show (Φ.comp sEquiv.toMonoidHom) y * (Φ.comp sEquiv.toMonoidHom) xs =
      (Φ.comp sEquiv.toMonoidHom) xs * (Φ.comp sEquiv.toMonoidHom) y
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hT₀c hy)]
  have hinj : Function.Injective (Φ.comp sEquiv.toMonoidHom) := hΦ.comp sEquiv.injective
  refine not_isConj_of_two_pow_dvd ψ hK ?_
  rw [Subgroup.card_map_of_injective hinj, (hall T₀).1]
  exact pow_dvd_pow 2 (by norm_num)

theorem natCard_vStab_inf_of_dist_three
    {v u : CVert} (hvu : cgraph.dist v u = 3) :
    Nat.card (vStab v ⊓ vStab u : Subgroup Shat) = 13244506413465600 := by
  have h := native_distance_three_pair_is_full_local_centralizer_final hvu
  obtain ⟨-, -, -, -, -, hcard, -, -⟩ := h
  exact hcard

theorem centralizer_inf_cV0_mul
    {u : CVert} (hu : u ∈ sphereDistThree cv0) :
    (Subgroup.centralizer {(cV0 : Shat)} ⊓ Subgroup.centralizer {(cV0 : Shat) * clabelS u} :
      Subgroup Shat) = Subgroup.centralizer {clabelS cv0, clabelS u} := by
  have hcu := cV0_mul_clabelS_comm hu
  apply le_antisymm
  · intro s hs
    have h1 : s * cV0 = cV0 * s :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hs).1
    have h2 : s * ((cV0 : Shat) * clabelS u) = (cV0 * clabelS u) * s :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hs).2
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rcases hy with rfl | rfl
    · rw [← coe_cV0]
      exact h1.symm
    · refine mul_left_cancel (a := (cV0 : Shat)) ?_
      calc (cV0 : Shat) * (clabelS u * s) = cV0 * clabelS u * s := (mul_assoc _ _ _).symm
        _ = s * (cV0 * clabelS u) := h2.symm
        _ = s * cV0 * clabelS u := (mul_assoc _ _ _).symm
        _ = cV0 * s * clabelS u := by rw [h1]
        _ = cV0 * (s * clabelS u) := mul_assoc _ _ _
  · intro s hs
    have h1 : (cV0 : Shat) * s = s * cV0 := by
      have := Subgroup.mem_centralizer_iff.1 hs (clabelS cv0) (Set.mem_insert _ _)
      rwa [← coe_cV0] at this
    have h2 : clabelS u * s = s * clabelS u :=
      Subgroup.mem_centralizer_iff.1 hs (clabelS u) (Set.mem_insert_of_mem _ rfl)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 h1.symm,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc s * ((cV0 : Shat) * clabelS u) = s * cV0 * clabelS u := (mul_assoc _ _ _).symm
      _ = cV0 * s * clabelS u := by rw [h1]
      _ = cV0 * (s * clabelS u) := mul_assoc _ _ _
      _ = cV0 * (clabelS u * s) := by rw [h2]
      _ = cV0 * clabelS u * s := (mul_assoc _ _ _).symm

theorem natCard_centralizer_inf_cV0_mul
    {u : CVert} (hu : u ∈ sphereDistThree cv0) :
    Nat.card (Subgroup.centralizer {(cV0 : Shat)} ⊓
      Subgroup.centralizer {(cV0 : Shat) * clabelS u} : Subgroup Shat) = 13244506413465600 := by
  rw [centralizer_inf_cV0_mul hu,
    centralizer_pair_eq_inf native_global_label_bijection_and_full_vertex_centralizer.1]
  exact natCard_vStab_inf_of_dist_three (mem_sphereDistThree.1 hu)

theorem h2C_of_FA_FB
    (hF : ∀ y : vStab cv0, orderOf y = 2 →
      Nat.card (Subgroup.centralizer {y}) = 13244506413465600 → y ∈ FA ∪ FB)
    (hFAB : ∀ y ∈ FA, ¬ IsConj y (cV0 * y)) :
    ∀ y : vStab cv0, orderOf y = 2 →
      Nat.card (Subgroup.centralizer {y}) = 13244506413465600 → ¬ IsConj y (cV0 * y) := by
  intro y hy hc h
  rcases hF y hy hc with hA | hB
  · exact hFAB y hA h
  · have hcc : cV0 * cV0 = 1 := (orderOf_two_iff.1 orderOf_cV0).1
    have e : cV0 * (cV0 * y) = y := by rw [← mul_assoc, hcc, one_mul]
    exact hFAB _ hB (by rw [e]; exact h.symm)

theorem map_mem_centralizer_of_commute {S : Type*} [Group S] (Φ : S →* G) {a b : S}
    (h : a * b = b * a) :
    Φ a ∈ Subgroup.centralizer {Φ b} :=
  Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, h])

theorem natCard_centralizer_eq_inf {K : Subgroup G} (x : K) :
    Nat.card (Subgroup.centralizer {x}) =
      Nat.card (Subgroup.centralizer {(x : G)} ⊓ K : Subgroup G) := by
  have e : Subgroup.centralizer {x} = (Subgroup.centralizer {(x : G)}).subgroupOf K := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
    rfl
  rw [e, ← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]

theorem natCard_centralizer_inf_map {S : Type*} [Group S] {Φ : S →* G}
    (hinj : Function.Injective Φ) {a b : S} (h : Subgroup.centralizer {Φ a} ≤ Φ.range) :
    Nat.card (Subgroup.centralizer {Φ a} ⊓ Subgroup.centralizer {Φ b} : Subgroup G) =
      Nat.card (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b} : Subgroup S) := by
  have e : Subgroup.centralizer {Φ a} ⊓ Subgroup.centralizer {Φ b} =
      (Subgroup.centralizer {a} ⊓ Subgroup.centralizer {b}).map Φ := by
    ext x
    constructor
    · intro hx
      have hx1 := (Subgroup.mem_inf.1 hx).1
      have hx2 := (Subgroup.mem_inf.1 hx).2
      obtain ⟨s, rfl⟩ := h hx1
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at hx1 hx2
      exact ⟨s, ⟨Subgroup.mem_centralizer_singleton_iff.2 (hinj hx1),
        Subgroup.mem_centralizer_singleton_iff.2 (hinj hx2)⟩, rfl⟩
    · rintro ⟨s, ⟨hs1, hs2⟩, rfl⟩
      exact ⟨map_mem_centralizer_of_commute Φ (Subgroup.mem_centralizer_singleton_iff.1 hs1),
        map_mem_centralizer_of_commute Φ (Subgroup.mem_centralizer_singleton_iff.1 hs2)⟩
  rw [e, Subgroup.card_map_of_injective hinj]

theorem conj_mul_of_swap {K : Type*} [Group K] {t a σ : G}
    (θ : Subgroup.centralizer {t} ≃* K) (ha : a ∈ Subgroup.centralizer {t})
    (hσ : σ ∈ Subgroup.centralizer {t}) (hσa : σ * a * σ⁻¹ = a * t) :
    θ ⟨σ, hσ⟩ * θ ⟨a, ha⟩ * (θ ⟨σ, hσ⟩)⁻¹ =
      θ ⟨a, ha⟩ * θ ⟨t, mem_centralizer_singleton_self t⟩ := by
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  exact congrArg θ (Subtype.ext hσa)

theorem orderOf_eq_two_of_psi
    {d : G} (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0) :
    orderOf d = 2 := by
  have h := orderOf_cV0
  rw [← centralizer_equiv_self_eq_cV0 hd ψ, MulEquiv.orderOf_eq, Subgroup.orderOf_mk] at h
  exact h

theorem not_isConj_map_clabelS_mul
    {d : G} (hd : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (h2C : ∀ y : vStab cv0, orderOf y = 2 →
      Nat.card (Subgroup.centralizer {y}) = 13244506413465600 → ¬ IsConj y (cV0 * y))
    {u : CVert} (hu : u ∈ sphereDistThree cv0) :
    ¬ IsConj d (Φ ((cV0 : Shat) * clabelS u)) := by
  intro ht
  have hΦc : Φ (cV0 : Shat) = d := map_cV0_of_psiInvHom hd ψ hΦ
  have hinj : Function.Injective Φ := injective_of_map_cV0_ne_one Φ (hΦc.symm ▸ hd)
  have hCd : Subgroup.centralizer {Φ (cV0 : Shat)} ≤ Φ.range :=
    hΦc.symm ▸ centralizer_le_range_of_psiInvHom ψ hΦ
  have hcu := cV0_mul_clabelS_comm hu
  have hcp : (cV0 : Shat) * ((cV0 : Shat) * clabelS u) = (cV0 * clabelS u) * cV0 := by
    rw [mul_assoc (cV0 : Shat) (clabelS u), ← hcu]
  have hdt' := map_mem_centralizer_of_commute Φ hcp
  have hsw := exists_swap_of_dist_three (pathInput_of_ambient ambientRootOrbitsHyp)
    (mem_sphereDistThree.1 hu)
  obtain ⟨σ, hσ1, hσ2⟩ := hsw
  rw [← coe_cV0] at hσ1 hσ2
  have hσp : σ * ((cV0 : Shat) * clabelS u) = ((cV0 : Shat) * clabelS u) * σ :=
    calc σ * ((cV0 : Shat) * clabelS u) =
        σ * cV0 * σ⁻¹ * (σ * clabelS u * σ⁻¹) * σ := by group
      _ = cV0 * clabelS u * σ := by rw [hσ1, hσ2, hcu]
  have hσt := map_mem_centralizer_of_commute Φ hσp
  have e1 : σ * (cV0 : Shat) * σ⁻¹ = (cV0 : Shat) * ((cV0 : Shat) * clabelS u) :=
    hσ1.trans (by rw [← mul_assoc, cV0_mul_self_coe, one_mul])
  have hσa : Φ σ * Φ (cV0 : Shat) * (Φ σ)⁻¹ = Φ (cV0 : Shat) * Φ ((cV0 : Shat) * clabelS u) :=
    (congrArg₂ (· * ·) (map_mul Φ σ _).symm (map_inv Φ σ).symm).trans
      ((map_mul Φ _ _).symm.trans ((congrArg Φ e1).trans (map_mul Φ _ _)))
  obtain ⟨θ, hθ⟩ : ∃ θ : Subgroup.centralizer {Φ ((cV0 : Shat) * clabelS u)} ≃* vStab cv0,
      θ ⟨_, mem_centralizer_singleton_self _⟩ = cV0 := ⟨psiAt ψ ht, psiAt_self hd ψ ht⟩
  have hconj := conj_mul_of_swap θ hdt' hσt hσa
  have hconj' : θ ⟨_, hσt⟩ * θ ⟨_, hdt'⟩ * (θ ⟨_, hσt⟩)⁻¹ = cV0 * θ ⟨_, hdt'⟩ :=
    hconj.trans ((congrArg (θ ⟨_, hdt'⟩ * ·) hθ).trans
      (Subgroup.mem_centralizer_singleton_iff.1 (cV0_mem_centralizer (θ ⟨_, hdt'⟩))).symm)
  have hu2 : orderOf (θ ⟨_, hdt'⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, orderOf_injective Φ hinj, orderOf_coe_cV0]
  have hcard : Nat.card (Subgroup.centralizer {θ ⟨_, hdt'⟩}) = 13244506413465600 := by
    rw [← Nat.card_congr (centralizerEquiv θ ⟨_, hdt'⟩).toEquiv, natCard_centralizer_eq_inf,
      natCard_centralizer_inf_map hinj hCd, natCard_centralizer_inf_cV0_mul hu]
  exact h2C _ hu2 hcard (isConj_iff.2 ⟨_, hconj'⟩)

theorem not_isConj_of_rankS_eq_2168
    {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (Φ : Shat →* G) (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    {y : vStab cv0} (hy : orderOf y = 2) (hyr : rankS (y : Shat) = 2168) (hyD : y ∉ dH ψ)
    {s : Shat} (hs : orderOf s = 2) (hsr : rankS s = 2168) : ¬ IsConj d (Φ s) := by
  intro h
  have hy' : orderOf (y : Shat) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hc : IsConj (Φ s) (Φ y) := Φ.map_isConj (isConj_of_rankS_eq hs hy' (hsr.trans hyr.symm))
  apply hyD
  rw [mem_dH_iff, ← psiInvHom_apply, ← hΦ]
  exact h.trans hc

@[expose] def dZero (M : Subgroup G) (d : G) : Set G := {x | ∃ g ∈ M, g * d * g⁻¹ = x}

theorem self_mem_dZero (M : Subgroup G) (d : G) : d ∈ dZero M d :=
  ⟨1, M.one_mem, by group⟩

theorem conjugatesOf_inter_range
    {d : G} (hd : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (h2C : ∀ y : vStab cv0, orderOf y = 2 →
      Nat.card (Subgroup.centralizer {y}) = 13244506413465600 → ¬ IsConj y (cV0 * y))
    (h2D : ∃ y : vStab cv0, orderOf y = 2 ∧ rankS (y : Shat) = 2168 ∧ y ∉ dH ψ) :
    conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d := by
  have hΦc : Φ (cV0 : Shat) = d := map_cV0_of_psiInvHom hd ψ hΦ
  have hinj : Function.Injective Φ := injective_of_map_cV0_ne_one Φ (hΦc.symm ▸ hd)
  have hd2 : orderOf d = 2 := orderOf_eq_two_of_psi hd ψ
  ext x
  constructor
  · rintro ⟨hxD, s, rfl⟩
    have hxD' : IsConj d (Φ s) := hxD
    have hs2 : orderOf s = 2 := by
      obtain ⟨c, hc⟩ := hxD'
      rw [← orderOf_injective Φ hinj, ← SemiconjBy.orderOf_eq _ hc, hd2]
    rcases rankS_mem_of_orderOf hs2 with h | h | h | h
    · obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_rankS_eq orderOf_coe_cV0 hs2
        (rankS_cV0.trans h.symm))
      exact ⟨Φ g, ⟨g, rfl⟩, by rw [map_mul, map_mul, map_inv, hΦc]⟩
    · exact absurd (hxD'.trans (Φ.map_isConj (isConj_of_rankS_eq hs2 orderOf_sEquiv_xs
        (h.trans rankS_sEquiv_xs.symm)))) (not_isConj_map_sEquiv_xs ψ hinj)
    · obtain ⟨u, hu, hur⟩ := exists_rankS_clabelS_mul
      exact absurd (hxD'.trans (Φ.map_isConj (isConj_of_rankS_eq hs2
        (orderOf_cV0_mul_clabelS hu) (h.trans hur.symm))))
        (not_isConj_map_clabelS_mul hd ψ Φ hΦ h2C hu)
    · obtain ⟨y, hy2, hyr, hyD⟩ := h2D
      exact absurd hxD' (not_isConj_of_rankS_eq_2168 ψ Φ hΦ hy2 hyr hyD hs2 h)
  · rintro ⟨g, hg, rfl⟩
    exact ⟨isConj_iff.2 ⟨g, rfl⟩,
      Φ.range.mul_mem (Φ.range.mul_mem hg ⟨_, hΦc⟩) (Φ.range.inv_mem hg)⟩

section Control

variable {M : Subgroup G} {d : G}

theorem conj_of_mem_dZero {a b : G} (ha : a ∈ dZero M d) (hb : b ∈ dZero M d) :
    ∃ m ∈ M, m * a * m⁻¹ = b := by
  obtain ⟨g, hg, rfl⟩ := ha
  obtain ⟨h, hh, rfl⟩ := hb
  exact ⟨h * g⁻¹, M.mul_mem hh (M.inv_mem hg), by group⟩

theorem centralizer_le_of_mem_dZero (hC : ∀ m ∈ M, Subgroup.centralizer {m * d * m⁻¹} ≤ M)
    {a : G} (ha : a ∈ dZero M d) : Subgroup.centralizer {a} ≤ M := by
  obtain ⟨g, hg, rfl⟩ := ha
  exact hC g hg

theorem mem_of_conj_mem_dZero (hC : ∀ m ∈ M, Subgroup.centralizer {m * d * m⁻¹} ≤ M)
    {g a : G} (ha : a ∈ dZero M d) (hga : g * a * g⁻¹ ∈ dZero M d) : g ∈ M :=
  mem_of_conj_mem_of_centralizer_le (fun _ ha _ hb => conj_of_mem_dZero ha hb)
    (fun _ ha => centralizer_le_of_mem_dZero hC ha) ha hga

theorem smul_coe_eq_self_iff_conj_mem {a x : G} : a • (x : G ⧸ M) = x ↔ x⁻¹ * a * x ∈ M := by
  rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
  constructor
  · intro h
    simpa [mul_assoc] using M.inv_mem h
  · intro h
    simpa [mul_assoc] using M.inv_mem h

theorem existsUnique_fixed_coset (hdM : d ∈ M)
    (hC : ∀ m ∈ M, Subgroup.centralizer {m * d * m⁻¹} ≤ M)
    (hDM : ∀ x ∈ M, IsConj d x → x ∈ dZero M d) {a : G} (ha : IsConj d a) :
    ∃! q : G ⧸ M, a • q = q := by
  obtain ⟨g, hg⟩ := isConj_iff.1 ha
  refine ⟨(g : G ⧸ M), smul_coe_eq_self_iff_conj_mem.2 ?_, fun q hq => ?_⟩
  · have e : g⁻¹ * a * g = d := by rw [← hg]; group
    rw [e]
    exact hdM
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx := smul_coe_eq_self_iff_conj_mem.1 hq
    have hD : x⁻¹ * a * x ∈ dZero M d :=
      hDM _ hx (ha.trans (isConj_iff.2 ⟨x⁻¹, by group⟩))
    have e : x⁻¹ * g * d * (x⁻¹ * g)⁻¹ = x⁻¹ * a * x := by rw [← hg]; group
    exact QuotientGroup.eq.2 (mem_of_conj_mem_dZero hC (self_mem_dZero M d) (e ▸ hD))

theorem odd_index_of_conj_class [Finite G] (hd : orderOf d = 2) (hdM : d ∈ M)
    (hC : ∀ m ∈ M, Subgroup.centralizer {m * d * m⁻¹} ≤ M)
    (hDM : ∀ x ∈ M, IsConj d x → x ∈ dZero M d) : Odd M.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : IsPGroup 2 (Subgroup.zpowers d) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd, pow_one])
  have hmod := hZ.card_modEq_card_fixedPoints (G ⧸ M)
  have hU := existsUnique_fixed_coset hdM hC hDM (IsConj.refl d)
  have h1 : d • ((1 : G) : G ⧸ M) = ((1 : G) : G ⧸ M) :=
    smul_coe_eq_self_iff_conj_mem.2 (by rw [inv_one, one_mul, mul_one]; exact hdM)
  have hfix : MulAction.fixedPoints (Subgroup.zpowers d) (G ⧸ M) = {((1 : G) : G ⧸ M)} := by
    ext q
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro h
      exact hU.unique (h ⟨d, Subgroup.mem_zpowers d⟩) h1
    · rintro rfl ⟨z, hz⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      show d ^ k • ((1 : G) : G ⧸ M) = ((1 : G) : G ⧸ M)
      rw [smul_coe_eq_self_iff_conj_mem, inv_one, one_mul, mul_one]
      exact zpow_mem hdM k
  have hone : Nat.card ({((1 : G) : G ⧸ M)} : Set (G ⧸ M)) = 1 := Nat.card_unique
  rw [hfix, hone] at hmod
  have h2 : M.index % 2 = 1 := hmod
  exact Nat.odd_iff.2 h2

theorem exists_sylow_eq_map_of_odd_index [Finite G] (hM : Odd M.index) (P : Sylow 2 M) :
    ∃ T : Sylow 2 G, (T : Subgroup G) = (P : Subgroup M).map M.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ((P : Subgroup M).map M.subtype) = 2 ^ (Nat.card G).factorization 2 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, P.card_eq_multiplicity,
      ← M.card_mul_index, Nat.factorization_mul Nat.card_pos.ne' hM.pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hM.not_two_dvd_nat, add_zero]
  exact ⟨Sylow.ofCard _ hcard, Sylow.coe_ofCard _ _⟩

theorem normalizer_le_of_mem_dZero (hC : ∀ m ∈ M, Subgroup.centralizer {m * d * m⁻¹} ≤ M)
    (hDM : ∀ x ∈ M, IsConj d x → x ∈ dZero M d) {X : Subgroup G} (hXM : X ≤ M)
    (hXD : ∃ a ∈ X, a ∈ dZero M d) : Subgroup.normalizer (X : Set G) ≤ M :=
  normalizer_le_of_conj_class (fun _ ha _ hb => conj_of_mem_dZero ha hb)
    (fun _ ha => centralizer_le_of_mem_dZero hC ha) (D := {x | IsConj d x})
    (fun _ hx g => hx.trans (isConj_iff.2 ⟨g, rfl⟩))
    (fun _ ⟨g, _, hg⟩ => isConj_iff.2 ⟨g, hg⟩) (fun x hx hxM => hDM x hxM hx) hXM hXD

theorem not_isConj_of_mem_inf_conj (hC : ∀ m ∈ M, Subgroup.centralizer {m * d * m⁻¹} ≤ M)
    (hDM : ∀ x ∈ M, IsConj d x → x ∈ dZero M d) {g : G} (hg : g ∉ M) {x : G}
    (hx : x ∈ M ⊓ M.map (MulAut.conj g).toMonoidHom) : ¬ IsConj d x := by
  intro hdx
  obtain ⟨hxM, y, hyM, hyx⟩ := hx
  have hyx' : g * y * g⁻¹ = x := hyx
  have hdy : IsConj d y := hdx.trans (isConj_iff.2 ⟨g⁻¹, by rw [← hyx']; group⟩)
  exact hg (mem_of_conj_mem_dZero hC (hDM y hyM hdy) (hyx'.symm ▸ hDM x hxM hdx))

end Control

theorem completion_fusion
    [Finite G] {d : G} (hd : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) :
    (∀ a : G, IsConj d a → ∃! q : G ⧸ Φ.range, a • q = q) ∧ Odd Φ.range.index ∧
    (∃ m : ℕ, Odd m ∧ Nat.card G = 2 ^ 41 * m) ∧
    (∀ P : Sylow 2 Φ.range, ∃ T : Sylow 2 G,
      (T : Subgroup G) = (P : Subgroup Φ.range).map Φ.range.subtype) ∧
    (∀ X : Subgroup G, X ≤ Φ.range → (∃ a ∈ X, a ∈ dZero Φ.range d) →
      Subgroup.normalizer (X : Set G) ≤ Φ.range) ∧
    ∀ g ∉ Φ.range, ∀ x ∈ Φ.range ⊓ Φ.range.map (MulAut.conj g).toMonoidHom,
      ¬ IsConj d x := by
  have hΦc : Φ (cV0 : Shat) = d := map_cV0_of_psiInvHom hd ψ hΦ
  have hinj : Function.Injective Φ := injective_of_map_cV0_ne_one Φ (hΦc.symm ▸ hd)
  have hdM : d ∈ Φ.range := ⟨_, hΦc⟩
  have hC : ∀ m ∈ Φ.range, Subgroup.centralizer {m * d * m⁻¹} ≤ Φ.range := fun m hm =>
    (completion_centralizer hd ψ Φ hΦ).2.2 m hm
  have hD : ∀ x ∈ Φ.range, IsConj d x → x ∈ dZero Φ.range d := fun x hx hdx =>
    hDM ▸ (⟨hdx, hx⟩ : x ∈ conjugatesOf d ∩ (Φ.range : Set G))
  have hodd := odd_index_of_conj_class (orderOf_eq_two_of_psi hd ψ) hdM hC hD
  refine ⟨fun a ha => existsUnique_fixed_coset hdM hC hD ha, hodd, ?_,
    fun P => exists_sylow_eq_map_of_odd_index hodd P,
    fun X hXM hXD => normalizer_le_of_mem_dZero hC hD hXM hXD,
    fun g hg x hx => not_isConj_of_mem_inf_conj hC hD hg hx⟩
  obtain ⟨m, hm, hcard⟩ := natCard_Sbp_two_part
  refine ⟨m * Φ.range.index, hm.mul hodd, ?_⟩
  rw [← Φ.range.card_mul_index, ← mul_assoc, ← hcard, Nat.card_congr sEquiv.toEquiv,
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

end CFSG.Monster.B.GSide

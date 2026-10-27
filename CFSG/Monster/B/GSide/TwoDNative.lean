module

public import CFSG.Monster.B.TwoA.Sp8.Orth8Plus
public import CFSG.Monster.B.GSide.TwoBNative
public import CFSG.Monster.B.GSide.CompletionFusion
public import CFSG.Monster.B.CTIB.SylowCenter
public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
public import CFSG.ClassicalGroups.Orthogonal.Simple
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
public import Certificates.Certificate3122
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

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open MulOpposite CFSG.Blueprint CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.CTIB
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Amalgam

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def t2DS :
    Shat := ⟨t2D, t2D_mem_Shat⟩

@[expose] def T9S : Subgroup Shat := T9.subgroupOf Shat

@[expose] def A8S : Subgroup Shat := A8.subgroupOf Shat

@[expose] def LgrpS : Subgroup Shat := Lgrp.subgroupOf Shat

@[expose] def P4pS :
    Subgroup Shat := P4p.subgroupOf Shat

theorem coe_t2DS :
    (t2DS : Dfull) = t2D := rfl

theorem mem_T9S
    {s : Shat} : s ∈ T9S ↔ (s : Dfull) ∈ T9 := Subgroup.mem_subgroupOf

theorem mem_A8S
    {s : Shat} : s ∈ A8S ↔ (s : Dfull) ∈ A8 := Subgroup.mem_subgroupOf

theorem mem_LgrpS
    {s : Shat} : s ∈ LgrpS ↔ (s : Dfull) ∈ Lgrp := Subgroup.mem_subgroupOf

theorem mem_P4pS
    {s : Shat} : s ∈ P4pS ↔ (s : Dfull) ∈ P4p := Subgroup.mem_subgroupOf

theorem t2DS_mem_T9S :
    t2DS ∈ T9S := t2D_mem_T9

theorem t2DS_not_mem_A8S :
    t2DS ∉ A8S := t2D_not_mem_A8

theorem t2DS_mul_self :
    t2DS * t2DS = 1 := Subtype.ext t2D_mul_self

theorem t2DS_ne_one :
    t2DS ≠ 1 := fun h => t2DS_not_mem_A8S (h ▸ A8S.one_mem)

theorem orderOf_t2DS :
    orderOf t2DS = 2 :=
  orderOf_eq_prime (by rw [sq, t2DS_mul_self]) t2DS_ne_one

theorem cV0_mem_T9S :
    (cV0 : Shat) ∈ T9S := by
  rw [mem_T9S, coe_cV0_dfull]
  exact cQ_mem_T9

theorem A8S_le_T9S :
    A8S ≤ T9S := fun _ hx => mem_T9S.2 (A8_le_T9 (mem_A8S.1 hx))

theorem T9S_mul_self
    {x : Shat} (hx : x ∈ T9S) : x * x = 1 := by
  have h := T9_sq ⟨x, mem_T9S.1 hx⟩
  rw [sq] at h
  exact Subtype.ext (show (x : Dfull) * x = 1 from congrArg Subtype.val h)

theorem T9S_comm
    {x y : Shat} (hx : x ∈ T9S) (hy : y ∈ T9S) : x * y = y * x :=
  Subtype.ext (show (x : Dfull) * y = y * x from
    congrArg Subtype.val (T9_comm ⟨x, mem_T9S.1 hx⟩ ⟨y, mem_T9S.1 hy⟩))

theorem T9S_elemAb :

    (∀ x ∈ T9S, x * x = 1) ∧ (∀ x ∈ T9S, ∀ y ∈ T9S, x * y = y * x) ∧
    A8S ≤ T9S :=
  ⟨fun _ hx => T9S_mul_self hx, fun _ hx _ hy => T9S_comm hx hy, A8S_le_T9S⟩

theorem exists_twoA_mem_T9S :
    ∃ a ∈ T9S, IsConj (cV0 : Shat) a :=
  ⟨cV0, cV0_mem_T9S, IsConj.refl _⟩

theorem mem_A8S_or_mul_t2DS_mem
    {x : Shat} (hx : x ∈ T9S) : x ∈ A8S ∨ x * t2DS ∈ A8S := by
  rcases (mem_T9_iff _).1 (mem_T9S.1 hx) with h | h
  · exact Or.inl (mem_A8S.2 h)
  · right
    rw [mem_A8S]
    show (x : Dfull) * (cQ * Psi vPlus) ∈ A8
    have hc : (x : Dfull) * (((cV0 : vStab cv0) : Shat) : Dfull) =
        (((cV0 : vStab cv0) : Shat) : Dfull) * x := congrArg Subtype.val (T9S_comm hx cV0_mem_T9S)
    rw [coe_cV0_dfull] at hc
    rw [← mul_assoc, hc]
    exact A8.mul_mem h (Psi_mem_A8 _)

theorem orderOf_xhatS : orderOf xhatS = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_xhat

theorem rankS_xhatS :
    rankS xhatS = 2048 := by
  rw [← sEquiv_xs]
  exact rankS_sEquiv_xs

theorem rankS_A8S
    (x : Shat) (hx : x ∈ A8S) (h1 : x ≠ 1) : orderOf x = 2 ∧ rankS x = 2048 := by
  have hx1 : (x : Dfull) ≠ 1 := fun h => h1 (Subtype.ext h)
  obtain ⟨g, hg, hgx⟩ := Xgrp_transitive xhat_mem_A8_e0 (mem_A8S.1 hx) TwoA.xhat_ne_one hx1
  have hc : IsConj xhatS x := isConj_iff.2 ⟨⟨g, Xgrp_le_Shat hg⟩, Subtype.ext hgx⟩
  refine ⟨orderOf_eq_prime (by rw [sq, T9S_mul_self (A8S_le_T9S hx)]) h1, ?_⟩
  rw [← rankS_conj hc, rankS_xhatS]

@[expose] def uPlusS :
    Shat := ⟨Psi vPlus, A8_le_Shat (Psi_mem_A8 _)⟩

theorem uPlusS_mem_A8S :
    uPlusS ∈ A8S := Psi_mem_A8 _

theorem uPlusS_ne_one :
    uPlusS ≠ 1 := fun h => by
  have h1 : Psi vPlus = Psi 0 := (congrArg Subtype.val h).trans Psi_zero'.symm
  exact absurd (Psi_inj h1) (by decide)

theorem t2DS_eq :
    t2DS = (cV0 : Shat) * uPlusS := Subtype.ext (by
  show cQ * Psi vPlus = (((cV0 : vStab cv0) : Shat) : Dfull) * Psi vPlus
  rw [coe_cV0_dfull])

theorem rankS_t2DS :
    rankS t2DS = 2168 := by
  have hw2 : uPlusS * uPlusS = 1 := T9S_mul_self (A8S_le_T9S uPlusS_mem_A8S)
  have hwr := (rankS_A8S _ uPlusS_mem_A8S uPlusS_ne_one).2
  have hcw : uPlusS * (cV0 : Shat) = (cV0 : Shat) * uPlusS :=
    T9S_comm (A8S_le_T9S uPlusS_mem_A8S) cV0_mem_T9S
  set w := sEquiv.symm uPlusS with hw
  have hw2' : w * w = 1 := by rw [hw, ← map_mul, hw2, map_one]
  have hcw' : w * labelS = labelS * w := by
    rw [hw, ← sEquiv_symm_cV0, ← map_mul, ← map_mul, hcw]
  have hrank : rankS t2DS = ((βr (labelS * w)) - 1).rank := by
    rw [rankS, t2DS_eq, map_mul, sEquiv_symm_cV0]
  rw [hrank]
  rcases frame_two_B (IsConj.refl labelS) hw2' hwr hcw' with ⟨-, g', hg'c, hg'w⟩ | ⟨g', hg'c, hg'w⟩
  · exfalso
    obtain ⟨g, hg, hgw, hgc⟩ := exists_conj_vPlus_xhat
    set G : Shat := ⟨g, Xgrp_le_Shat hg⟩ with hG
    have hGw : G * uPlusS * G⁻¹ = xhatS := Subtype.ext hgw
    have hGc : G * (cV0 : Shat) * G⁻¹ ∉ QhatS := by
      rw [mem_QhatS]
      show g * (((cV0 : vStab cv0) : Shat) : Dfull) * g⁻¹ ∉ Ehat
      rw [coe_cV0_dfull]
      exact hgc
    set u := sEquiv.symm G with hu
    have huw : u * w * u⁻¹ = xs := by
      rw [hu, hw, ← map_inv, ← map_mul, ← map_mul, hGw, ← sEquiv_xs, MulEquiv.symm_apply_apply]
    have huc : u * labelS * u⁻¹ ∉ Qs := by
      intro h
      apply hGc
      rw [← sEquiv_mem_QhatS] at h
      rwa [hu, ← sEquiv_symm_cV0, ← map_inv, ← map_mul, ← map_mul, MulEquiv.apply_symm_apply]
        at h
    have hJ : (g' * u⁻¹).unop ∈ Jbar := by
      apply centralizer_xs_comm
      calc g' * u⁻¹ * xs = g' * (u⁻¹ * xs * u) * u⁻¹ := by group
        _ = g' * w * u⁻¹ := by rw [show u⁻¹ * xs * u = w by rw [← huw]; group]
        _ = g' * w * g'⁻¹ * (g' * u⁻¹) := by group
        _ = xs * (g' * u⁻¹) := by rw [hg'w]
    apply huc
    have e : u * labelS * u⁻¹ = (g' * u⁻¹)⁻¹ * qS 1 * (g' * u⁻¹) := by
      rw [← hg'c]
      group
    rw [e]
    exact conj_mem_Qs hJ (qS_mem 1)
  · have e : labelS * w = g'⁻¹ * (rs 6 * xs) * g' := by
      rw [← hg'c, ← hg'w]
      group
    rw [e, rank_conj, rank_rs6_mul_xs]

theorem t2DS_spec :
    orderOf t2DS = 2 ∧ rankS t2DS = 2168 ∧ t2DS ∈ T9S ∧ t2DS ∉ A8S :=
  ⟨orderOf_t2DS, rankS_t2DS, t2DS_mem_T9S, t2DS_not_mem_A8S⟩

theorem rankS_mul_t2DS
    {x : Shat} (hx : x ∈ A8S) : rankS (x * t2DS) ≠ 2048 := by
  have hx' := mem_A8S.1 hx
  rw [← range_PsiHom] at hx'
  obtain ⟨u, hu⟩ := hx'
  have hxt : ((x * t2DS : Shat) : Dfull) = cQ * Psi (u.toAdd + vPlus) := by
    show (x : Dfull) * (cQ * Psi vPlus) = _
    rw [← hu, PsiHom_apply, ← mul_assoc, ← cQ_comm_Psi, mul_assoc, ← Psi_add]
  rcases zmod2_cases (qPoly (u.toAdd + vPlus)) with h0 | h1
  · obtain ⟨g, hg, hgc⟩ := mem_orbit_of_qPoly h0
    have hc : IsConj (cV0 : Shat) (x * t2DS) := isConj_iff.2 ⟨⟨g, Xgrp_le_Shat hg⟩,
      Subtype.ext (by
        show g * (((cV0 : vStab cv0) : Shat) : Dfull) * g⁻¹ = _
        rw [coe_cV0_dfull, hgc, hxt])⟩
    rw [← rankS_conj hc, rankS_cV0]
    decide
  · obtain ⟨g, hg, hgt⟩ := mem_orbit_t2D h1
    have hc : IsConj t2DS (x * t2DS) := isConj_iff.2 ⟨⟨g, Xgrp_le_Shat hg⟩,
      Subtype.ext (by
        show g * t2D * g⁻¹ = _
        rw [hgt, hxt])⟩
    rw [← rankS_conj hc, rankS_t2DS]
    decide

theorem eq_of_conj_eq_or_mul_t2DS
    (g : Shat) (hg : g ∈ Subgroup.centralizer {t2DS})
    (h : ∀ x ∈ T9S, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x * t2DS) :
    ∀ x ∈ T9S, g * x * g⁻¹ = x := by
  have hgt : g * t2DS * g⁻¹ = t2DS := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hg, mul_inv_cancel_right]
  have hA : ∀ x ∈ A8S, g * x * g⁻¹ = x := by
    intro x hx
    by_cases h1 : x = 1
    · rw [h1, mul_one, mul_inv_cancel]
    rcases h x (A8S_le_T9S hx) with e | e
    · exact e
    · exfalso
      have hr := rankS_conj (isConj_iff.2 ⟨g, rfl⟩ : IsConj x (g * x * g⁻¹))
      rw [e, (rankS_A8S _ hx h1).2] at hr
      exact rankS_mul_t2DS hx hr.symm
  intro x hx
  rcases mem_A8S_or_mul_t2DS_mem hx with hxA | hxA
  · exact hA x hxA
  · have e := hA _ hxA
    have ex : x = x * t2DS * t2DS := by rw [mul_assoc, t2DS_mul_self, mul_one]
    calc g * x * g⁻¹ = g * (x * t2DS * t2DS) * g⁻¹ := by rw [← ex]
      _ = g * (x * t2DS) * g⁻¹ * (g * t2DS * g⁻¹) := by group
      _ = x * t2DS * t2DS := by rw [e, hgt]
      _ = x := ex.symm

theorem isPGroup_centralizer_T9S :
    IsPGroup 2 (Subgroup.centralizer (T9S : Set Shat)) := by
  have hle : Subgroup.centralizer (T9S : Set Shat) ≤ LgrpS := by
    intro s hs
    rw [mem_LgrpS]
    rw [Lgrp, Subgroup.mem_centralizer_iff]
    intro a ha
    have h := (Subgroup.mem_centralizer_iff.1 hs) ⟨a, A8_le_Shat ha⟩
      (A8S_le_T9S (mem_A8S.2 ha))
    exact congrArg Subtype.val h
  have hL : IsPGroup 2 LgrpS := by
    refine IsPGroup.of_card (n := 25) ?_
    rw [LgrpS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((Lgrp_le_Xgrp).trans Xgrp_le_Shat)).toEquiv, natCard_Lgrp]
  exact hL.to_le hle

theorem oddCore_centralizer_t2DS :
    CFSG.oddCore ↥(Subgroup.centralizer {t2DS}) = ⊥ := by
  have h2 : orderOf (sEquiv.symm t2DS) = 2 := (orderOf_sEquiv_symm _).trans orderOf_t2DS
  have hr : ((βr (sEquiv.symm t2DS)) - 1).rank = 2168 := rankS_t2DS
  refine oddCore_eq_bot_of_equiv ((centralizerEquiv sEquiv (sEquiv.symm t2DS)).trans
    (MulEquiv.subgroupCongr ?_)) (oddCore_rank2168 h2 hr)
  rw [MulEquiv.apply_symm_apply]

theorem exists_twoA_commute
    (s : Shat) (hs : s * s = 1) :
    ∃ a : Shat, IsConj (cV0 : Shat) a ∧ a * s = s * a := by
  by_cases h1 : s = 1
  · exact ⟨cV0, IsConj.refl _, by rw [h1, mul_one, one_mul]⟩
  have hs2 : orderOf (sEquiv.symm s) = 2 :=
    (orderOf_sEquiv_symm _).trans (orderOf_eq_prime (by rw [sq, hs]) h1)
  obtain ⟨y, -, -, hy, hcomm⟩ := native_involution_commutes_rank_1860 _ hs2
  refine ⟨sEquiv y, ?_, ?_⟩
  · rw [← sEquiv_labelS_eq_cV0]
    exact isConj_sEquiv_iff.2 hy.symm
  · have h := congrArg sEquiv hcomm.eq
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
    exact h.symm

@[expose] def polQ (u w : V8) : ZMod 2 := qPoly (u + w) + qPoly u + qPoly w

theorem polar_qPlus (u w : V8) : QuadraticMap.polar qPlus u w = polQ u w := by
  have h : QuadraticMap.polar qPlus u w = b0 u w := by
    rw [← polarBilin_qPlus, QuadraticMap.polarBilin_apply_apply]
  rw [h, b0_eq_qPoly, polQ, sub_eq_add_neg, sub_eq_add_neg, ZMod.neg_eq_self_mod_two,
    ZMod.neg_eq_self_mod_two]

theorem qPlus_eq_one_iff
    (w : V8) : qPlus w = 1 ↔ qPoly (w + vPlus) = 0 := by
  rw [qPlus_apply]
  rcases zmod2_cases (qPoly (w + vPlus)) with h | h <;> rw [h] <;> decide

theorem reflect_qPlus_apply
    {w : V8} (hw : qPoly (w + vPlus) = 0) (u : V8) :
    CFSG.ClassicalGroups.Orthogonal.reflect qPlus w u = u + polQ u w • w := by
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one ((qPlus_eq_one_iff w).2 hw),
    polar_qPlus]

theorem exists_nonsingular_polQ : ∀ u : V8, u ≠ 0 →
    ∃ w : V8, qPoly (w + vPlus) = 0 ∧ polQ u w = 1 := by
  decide +kernel

theorem nonsingular_reach : ∀ w : V8, qPoly (w + vPlus) = 0 → w = bvec 8 2 ∨
    polQ w (bvec 8 2) = 1 ∨ ∃ m : V8, qPoly (m + vPlus) = 0 ∧ polQ w m = 1 ∧
      polQ m (bvec 8 2) = 1 := by
  decide +kernel

theorem nonsingular_span : ∀ u : V8, u = 0 ∨ qPoly (u + vPlus) = 0 ∨
    ∃ w : V8, qPoly (w + vPlus) = 0 ∧ qPoly (u + w + vPlus) = 0 := by
  decide +kernel

theorem polQ_comm (u w : V8) : polQ u w = polQ w u := by
  rw [polQ, polQ, add_comm u w, add_assoc, add_comm (qPoly u), ← add_assoc]

theorem bvec_two_nonsingular : qPoly (bvec 8 2 + vPlus) = 0 := by decide +kernel

theorem eq_bot_or_eq_top_of_reflect (U : AddSubgroup V8)
    (hU : ∀ w : V8, qPoly (w + vPlus) = 0 → ∀ u ∈ U, u + polQ u w • w ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hb : U = ⊥
  · exact Or.inl hb
  right
  have step : ∀ u ∈ U, ∀ w : V8, qPoly (w + vPlus) = 0 → polQ u w = 1 → w ∈ U := by
    intro u hu w hw h1
    have h := hU w hw u hu
    rw [h1, one_smul] at h
    have h2 := U.sub_mem h hu
    rw [add_sub_cancel_left] at h2
    exact h2
  obtain ⟨u, hu, hu0⟩ := (AddSubgroup.bot_or_exists_ne_zero U).resolve_left hb
  obtain ⟨w₀, hw₀, hw₀u⟩ := exists_nonsingular_polQ u hu0
  have hw₀U := step u hu w₀ hw₀ hw₀u
  have hroot : bvec 8 2 ∈ U := by
    rcases nonsingular_reach w₀ hw₀ with h | h | ⟨m, hm, h1, h2⟩
    · exact h ▸ hw₀U
    · exact step w₀ hw₀U _ bvec_two_nonsingular h
    · exact step m (step w₀ hw₀U m hm h1) _ bvec_two_nonsingular h2
  have hns : ∀ w : V8, qPoly (w + vPlus) = 0 → w ∈ U := by
    intro w hw
    rcases nonsingular_reach w hw with h | h | ⟨m, hm, h1, h2⟩
    · exact h.symm ▸ hroot
    · exact step _ hroot w hw ((polQ_comm _ _).trans h)
    · exact step m (step _ hroot m hm ((polQ_comm _ _).trans h2)) w hw
        ((polQ_comm _ _).trans h1)
  rw [eq_top_iff]
  intro v _
  rcases nonsingular_span v with h | h | ⟨w, hw, hvw⟩
  · rw [h]
    exact U.zero_mem
  · exact hns v h
  · have h := U.add_mem (hns _ hvw) (hns w hw)
    rw [add_assoc, ZModModule.add_self, add_zero] at h
    exact h

theorem eq_zero_of_reflect_fix {u : V8} (h : ∀ w : V8, qPoly (w + vPlus) = 0 → polQ u w = 0) :
    u = 0 := by
  by_contra hu
  obtain ⟨w, hw, h1⟩ := exists_nonsingular_polQ u hu
  rw [h w hw] at h1
  exact absurd h1 (by decide)

@[expose] def PsiS
    (v : V8) : Shat := ⟨Psi v, A8_le_Shat (Psi_mem_A8 v)⟩

theorem PsiS_mem_A8S
    (v : V8) : PsiS v ∈ A8S := Psi_mem_A8 v

theorem PsiS_add
    (v w : V8) : PsiS (v + w) = PsiS v * PsiS w := Subtype.ext (Psi_add v w)

theorem PsiS_zero :
    PsiS 0 = 1 := Subtype.ext Psi_zero'

theorem exists_PsiS
    {x : Shat} (hx : x ∈ A8S) : ∃ v, PsiS v = x := by
  have hx' := mem_A8S.1 hx
  rw [← range_PsiHom] at hx'
  obtain ⟨v, hv⟩ := hx'
  exact ⟨v.toAdd, Subtype.ext hv⟩

theorem PsiS_injective :
    Function.Injective PsiS := fun _ _ h => Psi_inj (congrArg Subtype.val h)

theorem exists_two_mem_A8S :
    ∃ a ∈ A8S, ∃ b ∈ A8S, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  refine ⟨PsiS (bvec 8 1), PsiS_mem_A8S _, PsiS (bvec 8 2), PsiS_mem_A8S _, ?_, ?_, ?_⟩
  · rw [← PsiS_zero]
    exact fun h => absurd (PsiS_injective h) (by decide)
  · rw [← PsiS_zero]
    exact fun h => absurd (PsiS_injective h) (by decide)
  · exact fun h => absurd (PsiS_injective h) (by decide)

theorem exists_P4pS_of_orthogonal
    {M : V8 ≃ₗ[ZMod 2] V8}
    (hM : M ∈ TauCeti.QuadraticMap.orthogonalGroup qPlus) :
    ∃ g ∈ Subgroup.centralizer {t2DS}, ∀ v, g * PsiS v * g⁻¹ = PsiS (M v) := by
  obtain ⟨x, hx⟩ := p4pProj_surjective ⟨M, hM⟩
  have hxM : rhoX (Subgroup.inclusion P4p_le_Xgrp x) = M := congrArg Subtype.val hx
  refine ⟨⟨x, Xgrp_le_Shat (P4p_le_Xgrp x.2)⟩, ?_, fun v => ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 x.2.2)
  · apply Subtype.ext
    show (x : Dfull) * Psi v * (x : Dfull)⁻¹ = Psi (M v)
    rw [← hxM, Psi_rhoX]
    rfl

theorem zpowers_t2DS_eq
    (x : Shat) : x ∈ Subgroup.zpowers t2DS ↔ x = 1 ∨ x = t2DS :=
  Short.mem_zpowers_iff_of_orderOf_eq_two orderOf_t2DS

theorem eq_of_invariant_T9S
    (R : Subgroup Shat) (hRT : R ≤ T9S)
    (hR : ∀ g ∈ Subgroup.centralizer {t2DS}, ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    R = ⊥ ∨ R = Subgroup.zpowers t2DS ∨ R = A8S ∨ R = T9S := by
  let U : AddSubgroup V8 :=
    { carrier := {v | PsiS v ∈ R}
      add_mem' := fun ha hb => by
        show PsiS _ ∈ R
        rw [PsiS_add]
        exact R.mul_mem ha hb
      zero_mem' := by
        show PsiS 0 ∈ R
        rw [PsiS_zero]
        exact R.one_mem
      neg_mem' := fun {a} ha => by
        show PsiS (-a) ∈ R
        rwa [ZModModule.neg_eq_self] }
  have hmemU : ∀ v, v ∈ U ↔ PsiS v ∈ R := fun _ => Iff.rfl
  have hUinv : ∀ w : V8, qPoly (w + vPlus) = 0 → ∀ u ∈ U, u + polQ u w • w ∈ U := by
    intro w hw u hu
    obtain ⟨g, hg, hgv⟩ := exists_P4pS_of_orthogonal
      (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup qPlus w)
    rw [hmemU, ← reflect_qPlus_apply hw, ← hgv]
    exact hR g hg _ hu
  have hA : ∀ a ∈ A8S, a ∈ R ↔ ∃ v ∈ U, PsiS v = a := by
    intro a ha
    obtain ⟨v, rfl⟩ := exists_PsiS ha
    exact ⟨fun h => ⟨v, h, rfl⟩, fun ⟨w, hw, e⟩ => e ▸ hw⟩
  rcases eq_bot_or_eq_top_of_reflect U hUinv with hU | hU
  ·
    have hRA : ∀ r ∈ R, r ∈ A8S → r = 1 := by
      intro r hr hrA
      obtain ⟨v, hv, rfl⟩ := (hA r hrA).1 hr
      rw [hU, AddSubgroup.mem_bot] at hv
      rw [hv, PsiS_zero]
    have hR1 : ∀ r ∈ R, r = 1 ∨ r = t2DS := by
      intro r hr
      rcases mem_A8S_or_mul_t2DS_mem (hRT hr) with hrA | hrA
      · exact Or.inl (hRA r hr hrA)
      · right
        obtain ⟨u, hu⟩ := exists_PsiS hrA
        have hr' : r = PsiS u * t2DS := by rw [hu, mul_assoc, t2DS_mul_self, mul_one]
        have hu0 : u = 0 := by
          refine eq_zero_of_reflect_fix fun w hw => ?_
          obtain ⟨g, hg, hgv⟩ := exists_P4pS_of_orthogonal
            (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup qPlus w)
          have hgt : g * t2DS * g⁻¹ = t2DS := by
            rw [Subgroup.mem_centralizer_singleton_iff.1 hg, mul_inv_cancel_right]
          have hgr : g * r * g⁻¹ =
              PsiS (CFSG.ClassicalGroups.Orthogonal.reflect qPlus w u) * t2DS := by
            rw [hr', show g * (PsiS u * t2DS) * g⁻¹ = g * PsiS u * g⁻¹ * (g * t2DS * g⁻¹) by
              group, hgv, hgt]
          have hc : t2DS * PsiS (CFSG.ClassicalGroups.Orthogonal.reflect qPlus w u) =
              PsiS (CFSG.ClassicalGroups.Orthogonal.reflect qPlus w u) * t2DS :=
            T9S_comm t2DS_mem_T9S (A8S_le_T9S (PsiS_mem_A8S _))
          have hprod : r * (g * r * g⁻¹) =
              PsiS (u + CFSG.ClassicalGroups.Orthogonal.reflect qPlus w u) := by
            rw [hgr, hr', PsiS_add]
            calc PsiS u * t2DS * (PsiS (CFSG.ClassicalGroups.Orthogonal.reflect qPlus w u) *
                  t2DS) = PsiS u * (t2DS * PsiS (CFSG.ClassicalGroups.Orthogonal.reflect qPlus w
                    u)) * t2DS := by group
              _ = PsiS u * (PsiS (CFSG.ClassicalGroups.Orthogonal.reflect qPlus w u) * t2DS) *
                    t2DS := by rw [hc]
              _ = PsiS u * PsiS (CFSG.ClassicalGroups.Orthogonal.reflect qPlus w u) *
                    (t2DS * t2DS) := by group
              _ = _ := by rw [t2DS_mul_self, mul_one]
          have h1 := hRA _ (R.mul_mem hr (hR g hg r hr)) (by rw [hprod]; exact PsiS_mem_A8S _)
          rw [hprod] at h1
          have h2 : u + CFSG.ClassicalGroups.Orthogonal.reflect qPlus w u = 0 :=
            Psi_inj ((congrArg Subtype.val h1).trans Psi_zero'.symm)
          rw [reflect_qPlus_apply hw, ← add_assoc, ZModModule.add_self, zero_add] at h2
          rcases smul_eq_zero.1 h2 with h | h
          · exact h
          · exfalso
            rw [h, zero_add, qPoly_vPlus] at hw
            exact absurd hw (by decide)
        have h1 : r * t2DS = 1 := by rw [← hu, hu0, PsiS_zero]
        calc r = r * t2DS * t2DS := by rw [mul_assoc, t2DS_mul_self, mul_one]
          _ = t2DS := by rw [h1, one_mul]
    by_cases ht : t2DS ∈ R
    · refine Or.inr (Or.inl (le_antisymm (fun r hr => ?_) ?_))
      · rw [zpowers_t2DS_eq]
        exact hR1 r hr
      · rw [Subgroup.zpowers_le]
        exact ht
    · refine Or.inl (eq_bot_iff.2 fun r hr => ?_)
      rcases hR1 r hr with h | h
      · exact (Subgroup.mem_bot).2 h
      · exact absurd (h ▸ hr) ht
  ·
    have hAR : A8S ≤ R := fun a ha => (hA a ha).2 (by
      obtain ⟨v, rfl⟩ := exists_PsiS ha
      exact ⟨v, hU ▸ AddSubgroup.mem_top v, rfl⟩)
    by_cases hRA : R ≤ A8S
    · exact Or.inr (Or.inr (Or.inl (le_antisymm hRA hAR)))
    · right; right; right
      obtain ⟨r, hr, hrA⟩ := IsConcreteLE.not_le_iff_exists.1 hRA
      have hrt : r * t2DS ∈ A8S :=
        (mem_A8S_or_mul_t2DS_mem (hRT hr)).resolve_left hrA
      have htR : t2DS ∈ R := by
        have h := R.mul_mem (R.inv_mem hr) (hAR hrt)
        rwa [inv_mul_cancel_left] at h
      refine le_antisymm hRT fun x hx => ?_
      rcases mem_A8S_or_mul_t2DS_mem hx with hxA | hxA
      · exact hAR hxA
      · have h := R.mul_mem (hAR hxA) htR
        rwa [mul_assoc, t2DS_mul_self, mul_one] at h

@[expose] def rhoPlusS :
    P4pS →* TauCeti.QuadraticMap.orthogonalGroup qPlus :=
  p4pProj.comp (Subgroup.subgroupOfEquivOfLe (P4p_le_Xgrp.trans Xgrp_le_Shat)).toMonoidHom

theorem rhoPlusS_surjective :
    Function.Surjective rhoPlusS :=
  p4pProj_surjective.comp (Subgroup.subgroupOfEquivOfLe _).surjective

theorem rhoPlusS_eq_one_iff
    (g : P4pS) :
    rhoPlusS g = 1 ↔ ∀ x ∈ T9S, (g : Shat) * x * (g : Shat)⁻¹ = x := by
  have hL : rhoPlusS g = 1 ↔ ((g : Shat) : Dfull) ∈ Lgrp := by
    show p4pProj (Subgroup.subgroupOfEquivOfLe _ g) = 1 ↔ _
    rw [← MonoidHom.mem_ker, ker_p4pProj, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hgt : (g : Shat) * t2DS = t2DS * g :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (mem_P4pS.1 g.2).2)
  rw [hL, Lgrp, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have hc : ∀ y ∈ A8S, y * (g : Shat) = g * y := fun y hy => Subtype.ext (h _ (mem_A8S.1 hy))
    rw [mul_inv_eq_iff_eq_mul]
    rcases mem_A8S_or_mul_t2DS_mem hx with hxA | hxA
    · exact (hc x hxA).symm
    · calc (g : Shat) * x = g * (x * t2DS) * t2DS := by
            rw [mul_assoc, mul_assoc, t2DS_mul_self, mul_one]
        _ = x * t2DS * g * t2DS := by rw [hc _ hxA]
        _ = x * (t2DS * g) * t2DS := by rw [mul_assoc x t2DS]
        _ = x * (g * t2DS) * t2DS := by rw [hgt]
        _ = x * g := by simp only [mul_assoc, t2DS_mul_self, mul_one]
  · intro h a ha
    have e := h ⟨a, A8_le_Shat ha⟩ (A8S_le_T9S (mem_A8S.2 ha))
    rw [mul_inv_eq_iff_eq_mul] at e
    exact (congrArg Subtype.val e).symm

@[expose] def OmegaPlus : Subgroup (TauCeti.QuadraticMap.orthogonalGroup qPlus) := commutator _

instance OmegaPlus_normal : OmegaPlus.Normal := by
  show (commutator _).Normal
  infer_instance

@[expose] def qPlusCols : List ℕ := [1, 4, 31, 113, 128, 8, 47, 114]

@[expose] def qPlusInvCols : List ℕ := [1, 137, 2, 32, 174, 234, 77, 16]

@[expose] def qPlusMat : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => bvec 8 (qPlusCols.getD j 0) i

@[expose] def qPlusInvMat : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  Matrix.of fun i j => bvec 8 (qPlusInvCols.getD j 0) i

theorem qPlusMat_mul_inv : qPlusMat * qPlusInvMat = 1 := by decide +kernel

theorem qPlusInvMat_mul : qPlusInvMat * qPlusMat = 1 := by decide +kernel

theorem qPlus_hyperbolic : ∀ v : V8, ∑ i : Fin 4, qPlusInvMat.mulVec v (Fin.castAdd 4 i) *
    qPlusInvMat.mulVec v (Fin.natAdd 4 i) = qPoly (v + vPlus) + 1 := by
  decide +kernel

@[expose] def qPlusCoord : V8 ≃ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2) :=
  (Matrix.toLinearEquiv' qPlusInvMat ⟨qPlusMat, qPlusMat_mul_inv, qPlusInvMat_mul⟩).trans
    (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) finSumFinEquiv)

theorem qPlusCoord_apply (v : V8) (s : Fin 4 ⊕ Fin 4) :
    qPlusCoord v s = qPlusInvMat.mulVec v (finSumFinEquiv s) := rfl

theorem quadPlus_qPlusCoord (v : V8) :
    CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2) (qPlusCoord v) = qPlus v := by
  rw [CFSG.LieType.Universal.Spin.quadPlus_apply, qPlus_apply, ← qPlus_hyperbolic v]
  rfl

@[expose] def qPlusIsom :
    qPlus.IsometryEquiv (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)) :=
  { qPlusCoord with map_app' := quadPlus_qPlusCoord }

theorem scalars_eq_bot_zmod2 (W : Type*) [AddCommGroup W] [Module (ZMod 2) W] :
    CFSG.ClassicalGroups.Orthogonal.scalars (ZMod 2) W = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Orthogonal.mem_scalars.1 hg
  rw [Subgroup.mem_bot]
  refine LinearEquiv.ext fun v => ?_
  show g v = v
  rcases zmod2_cases c with h | h
  · have h0 : v = 0 := by
      have e := g.symm_apply_apply v
      rw [hc v, h, zero_smul, map_zero] at e
      exact e.symm
    rw [h0, map_zero]
  · rw [hc v, h, one_smul]

theorem isSimpleGroup_OmegaPlus : IsSimpleGroup OmegaPlus := by
  let e := TauCeti.QuadraticMap.orthogonalGroupCongr qPlusIsom
  have hmap : OmegaPlus.map (e : TauCeti.QuadraticMap.orthogonalGroup qPlus →*
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2))) =
      commutator (TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2))) := by
    rw [OmegaPlus, map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ e.surjective]
    rfl
  have hE := (Subgroup.map_subtype_commutator (TauCeti.QuadraticMap.orthogonalGroup
    (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)))).trans
    (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus (by norm_num))
  have hbot : (CFSG.ClassicalGroups.Orthogonal.scalars (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2)).subgroupOf
      (CFSG.ClassicalGroups.Orthogonal.elementaryGroup
        (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2))) = ⊥ := by
    rw [scalars_eq_bot_zmod2, Subgroup.bot_subgroupOf]
  have : IsSimpleGroup (CFSG.ClassicalGroups.Orthogonal.ProjElementary
      (CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_projElementary_quadPlus (by norm_num)
  exact MulEquiv.isSimpleGroup ((((e.subgroupMap OmegaPlus).trans
    (MulEquiv.subgroupCongr hmap)).trans
    (((commutator _).equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr hE))).trans
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)))

theorem eq_of_reflect_qPlus_eq
    {w w' : V8} (hw : qPoly (w + vPlus) = 0)
    (hw' : qPoly (w' + vPlus) = 0)
    (h : CFSG.ClassicalGroups.Orthogonal.reflect qPlus w =
      CFSG.ClassicalGroups.Orthogonal.reflect qPlus w') : w = w' := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_add, qPoly_vPlus] at hw
    exact absurd hw (by decide)
  obtain ⟨m, -, hmw⟩ := exists_nonsingular_polQ w hw0
  have h1 := LinearEquiv.congr_fun h m
  rw [reflect_qPlus_apply hw, reflect_qPlus_apply hw', polQ_comm m w, hmw, one_smul] at h1
  have h2 := add_left_cancel h1
  rcases zmod2_cases (polQ m w') with h3 | h3
  · rw [h3, zero_smul] at h2
    exact absurd h2 hw0
  · rw [h3, one_smul] at h2
    exact h2

theorem center_orthogonalGroup_qPlus :
    Subgroup.center (TauCeti.QuadraticMap.orthogonalGroup qPlus) = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  have hfix : ∀ w : V8, qPoly (w + vPlus) = 0 → (g : V8 ≃ₗ[ZMod 2] V8) w = w := by
    intro w hw
    have hgw : qPoly ((g : V8 ≃ₗ[ZMod 2] V8) w + vPlus) = 0 := by
      rw [← qPlus_eq_one_iff, CFSG.ClassicalGroups.Orthogonal.map_of_mem g.2, qPlus_eq_one_iff]
      exact hw
    refine eq_of_reflect_qPlus_eq hgw hw ?_
    rw [← CFSG.ClassicalGroups.Orthogonal.reflect_conj g.2 w, mul_inv_eq_iff_eq_mul]
    have hc := Subgroup.mem_center_iff.1 hg
      ⟨_, CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup qPlus w⟩
    exact (congrArg Subtype.val hc).symm
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  show (g : V8 ≃ₗ[ZMod 2] V8) v = v
  rcases nonsingular_span v with h | h | ⟨w, hw, hvw⟩
  · rw [h, map_zero]
  · exact hfix v h
  · have e : v = v + w + w := by rw [add_assoc, ZModModule.add_self, add_zero]
    rw [e, map_add, hfix _ hvw, hfix w hw]

theorem le_OmegaPlus_of_normal
    (R : Subgroup (TauCeti.QuadraticMap.orthogonalGroup qPlus))
    (hR : R.Normal) (hR1 : R ≠ ⊥) : OmegaPlus ≤ R := by
  have hs := isSimpleGroup_OmegaPlus
  have hRn := hR.subgroupOf OmegaPlus
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf OmegaPlus) with h | h
  · exfalso
    apply hR1
    have hc : ⁅R, ⊤⁆ ≤ R ⊓ OmegaPlus :=
      le_inf (Subgroup.commutator_le_left R ⊤)
        (show ⁅R, ⊤⁆ ≤ ⁅⊤, ⊤⁆ from Subgroup.commutator_mono le_top le_rfl)
    rw [(Subgroup.subgroupOf_eq_bot.1 h).eq_bot] at hc
    have hc' : ⁅R, ⊤⁆ = ⊥ := le_bot_iff.1 hc
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top, Subgroup.centralizer_univ,
      center_orthogonalGroup_qPlus] at hc'
    exact le_bot_iff.1 hc'
  · exact Subgroup.subgroupOf_eq_top.1 h

theorem orthogonalGroup_qPlus_eq_closure :
    TauCeti.QuadraticMap.orthogonalGroup qPlus =
      Subgroup.closure (Set.range (CFSG.ClassicalGroups.Orthogonal.reflect qPlus)) := by
  have h8 : Module.finrank (ZMod 2) V8 = 8 := Module.finrank_fin_fun (ZMod 2)
  refine CFSG.ClassicalGroups.Orthogonal.orthogonalGroup_eq_closure_reflect ?_ (by omega)
    (Or.inl (by omega))
  rw [polarBilin_qPlus]
  exact nondegenerate_b0

theorem reflect_reflect_qPlus
    {w w' : V8} (hw : qPoly (w + vPlus) = 0)
    (hw' : qPoly (w' + vPlus) = 0) (h : polQ w w' = 1) :
    CFSG.ClassicalGroups.Orthogonal.reflect qPlus w
      (CFSG.ClassicalGroups.Orthogonal.reflect qPlus w' w) = w' := by
  have e : w + w' + w = w' := by rw [add_comm w w', add_assoc, ZModModule.add_self, add_zero]
  have h2 : polQ (w + w') w = 1 := by
    rw [polQ, e, ← h, polQ]
    ring
  rw [reflect_qPlus_apply hw', h, one_smul, reflect_qPlus_apply hw, h2, one_smul, e]

@[expose] def reflPlus (w : V8) : TauCeti.QuadraticMap.orthogonalGroup qPlus :=
  ⟨_, CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup qPlus w⟩

theorem of_reflPlus_eq
    {w w' : V8} (hw : qPoly (w + vPlus) = 0) (hw' : qPoly (w' + vPlus) = 0)
    (h : polQ w w' = 1) : Abelianization.of (reflPlus w') = Abelianization.of (reflPlus w) := by
  have e : reflPlus w' = reflPlus w * reflPlus w' * reflPlus w * (reflPlus w * reflPlus w')⁻¹ := by
    apply Subtype.ext
    show CFSG.ClassicalGroups.Orthogonal.reflect qPlus w' =
      CFSG.ClassicalGroups.Orthogonal.reflect qPlus w *
        CFSG.ClassicalGroups.Orthogonal.reflect qPlus w' *
        CFSG.ClassicalGroups.Orthogonal.reflect qPlus w *
        (CFSG.ClassicalGroups.Orthogonal.reflect qPlus w *
          CFSG.ClassicalGroups.Orthogonal.reflect qPlus w')⁻¹
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_conj (mul_mem
      (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup qPlus w)
      (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup qPlus w')) w,
      LinearEquiv.mul_apply, reflect_reflect_qPlus hw hw' h]
  rw [e, map_mul, map_mul, map_inv, mul_comm (Abelianization.of (reflPlus w * reflPlus w')),
    mul_inv_cancel_right]

theorem of_reflPlus_eq_root {w : V8} (hw : qPoly (w + vPlus) = 0) :
    Abelianization.of (reflPlus w) = Abelianization.of (reflPlus (bvec 8 2)) := by
  rcases nonsingular_reach w hw with h | h | ⟨m, hm, h1, h2⟩
  · rw [h]
  · exact of_reflPlus_eq bvec_two_nonsingular hw ((polQ_comm _ _).trans h)
  · exact (of_reflPlus_eq hm hw ((polQ_comm _ _).trans h1)).trans
      (of_reflPlus_eq bvec_two_nonsingular hm ((polQ_comm _ _).trans h2))

theorem index_OmegaPlus_dvd_two : OmegaPlus.index ∣ 2 := by
  set x := Abelianization.of (reflPlus (bvec 8 2)) with hx
  have hgen : ∀ g : TauCeti.QuadraticMap.orthogonalGroup qPlus,
      Abelianization.of g ∈ Subgroup.zpowers x := by
    have hle : TauCeti.QuadraticMap.orthogonalGroup qPlus ≤
        ((Subgroup.zpowers x).comap Abelianization.of).map
          (TauCeti.QuadraticMap.orthogonalGroup qPlus).subtype := by
      refine orthogonalGroup_qPlus_eq_closure.le.trans ((Subgroup.closure_le _).2 ?_)
      rintro _ ⟨w, rfl⟩
      refine ⟨reflPlus w, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      rcases zmod2_cases (qPoly (w + vPlus)) with h | h
      · rw [of_reflPlus_eq_root h]
        exact Subgroup.mem_zpowers x
      · have h0 : reflPlus w = 1 := Subtype.ext
          (CFSG.ClassicalGroups.Orthogonal.reflect_of_map_eq_zero (by rw [qPlus_apply, h]; rfl))
        rw [h0, map_one]
        exact Subgroup.one_mem _
    intro g
    obtain ⟨k, hk, hkg⟩ := hle g.2
    rw [← Subtype.ext hkg]
    exact hk
  have hx2 : x ^ 2 = 1 := by
    rw [hx, ← map_pow, sq]
    have e : reflPlus (bvec 8 2) * reflPlus (bvec 8 2) = 1 :=
      Subtype.ext (CFSG.ClassicalGroups.Orthogonal.reflect_mul_self qPlus _)
    rw [e, map_one]
  have htop : Subgroup.zpowers x = ⊤ :=
    eq_top_iff.2 fun y _ => QuotientGroup.induction_on y fun g => hgen g
  have h1 : OmegaPlus.index = Nat.card (Subgroup.zpowers x) := by
    rw [htop, Subgroup.card_top]
    rfl
  rw [h1, Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one hx2

theorem dvd_natCard_OmegaPlus :
    2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 ∣ Nat.card OmegaPlus := by
  have hcard := Subgroup.card_mul_index OmegaPlus
  rw [natCard_orthogonalGroup_qPlus] at hcard
  rcases (Nat.dvd_prime Nat.prime_two).1 index_OmegaPlus_dvd_two with h | h
  · rw [h, mul_one] at hcard
    rw [hcard]
    norm_num
  · rw [h] at hcard
    have h' : Nat.card OmegaPlus = 174182400 := by omega
    rw [h']
    norm_num

theorem conj_mem_A8S_of_le_normalizer
    (hN6 : Subgroup.centralizer {t2DS} ≤ Subgroup.normalizer (T9S : Set Shat))
    (g : Shat) (hg : g ∈ Subgroup.centralizer {t2DS}) (w : Shat) (hw : w ∈ A8S) :
    g * w * g⁻¹ ∈ A8S := by
  by_cases h1 : w = 1
  · rw [h1, mul_one, mul_inv_cancel]
    exact A8S.one_mem
  have hT : g * w * g⁻¹ ∈ T9S := (Subgroup.mem_normalizer_iff.1 (hN6 hg) w).1 (A8S_le_T9S hw)
  rcases mem_A8S_or_mul_t2DS_mem hT with h | h
  · exact h
  · exfalso
    have hr : rankS (g * w * g⁻¹) = 2048 :=
      (rankS_conj (isConj_iff.2 ⟨g, rfl⟩)).symm.trans (rankS_A8S w hw h1).2
    have e : g * w * g⁻¹ * t2DS * t2DS = g * w * g⁻¹ := by
      rw [mul_assoc (g * w * g⁻¹), t2DS_mul_self, mul_one]
    exact rankS_mul_t2DS h (by rw [e]; exact hr)

theorem mem_Xgrp_of_conj_A8S
    {g : Shat} (hg : ∀ w ∈ A8S, g * w * g⁻¹ ∈ A8S)
    (hg' : ∀ w ∈ A8S, g⁻¹ * w * g⁻¹⁻¹ ∈ A8S) : (g : Dfull) ∈ Xgrp := by
  rw [← normalizer_A8_eq, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hg ⟨h, A8_le_Shat hh⟩ hh
  · intro hh
    have hS : (g : Dfull) * h * (g : Dfull)⁻¹ ∈ Shat := A8_le_Shat hh
    have hA := mem_A8S.1 (hg' ⟨_, hS⟩ hh)
    have e : ((g⁻¹ * ⟨_, hS⟩ * g⁻¹⁻¹ : Shat) : Dfull) = h := by
      show (g : Dfull)⁻¹ * ((g : Dfull) * h * (g : Dfull)⁻¹) * (g : Dfull)⁻¹⁻¹ = h
      group
    rw [e] at hA
    exact hA

theorem centralizer_t2DS_eq_P4pS_of_le_normalizer
    (hN6 : Subgroup.centralizer {t2DS} ≤ Subgroup.normalizer (T9S : Set Shat)) :
    Subgroup.centralizer {t2DS} = P4pS := by
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · rw [mem_P4pS]
    refine ⟨mem_Xgrp_of_conj_A8S (conj_mem_A8S_of_le_normalizer hN6 g hg)
      (conj_mem_A8S_of_le_normalizer hN6 g⁻¹ (Subgroup.inv_mem _ hg)), ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg))
  · exact Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (mem_P4pS.1 hg).2))

@[expose] def rhoPlus
    (hN6 : Subgroup.centralizer {t2DS} ≤ Subgroup.normalizer (T9S : Set Shat)) :
    Subgroup.centralizer {t2DS} →* TauCeti.QuadraticMap.orthogonalGroup qPlus :=
  rhoPlusS.comp (MulEquiv.subgroupCongr (centralizer_t2DS_eq_P4pS_of_le_normalizer hN6)).toMonoidHom

theorem rhoPlus_surjective
    (hN6 : Subgroup.centralizer {t2DS} ≤ Subgroup.normalizer (T9S : Set Shat)) :
    Function.Surjective (rhoPlus hN6) :=
  rhoPlusS_surjective.comp (MulEquiv.subgroupCongr _).surjective

theorem rhoPlus_eq_one_iff
    (hN6 : Subgroup.centralizer {t2DS} ≤ Subgroup.normalizer (T9S : Set Shat))
    (g : Subgroup.centralizer {t2DS}) :
    rhoPlus hN6 g = 1 ↔ ∀ x ∈ T9S, (g : Shat) * x * (g : Shat)⁻¹ = x :=
  rhoPlusS_eq_one_iff _

theorem natCard_centralizer_of_rankS_eq_2168
    (hN6 : Subgroup.centralizer {t2DS} ≤ Subgroup.normalizer (T9S : Set Shat))
    (t : Shat) (ht : orderOf t = 2) (hr : rankS t = 2168) :
    Nat.card (Subgroup.centralizer {t}) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_rankS_eq orderOf_t2DS ht (rankS_t2DS.trans hr.symm))
  have h1 : Nat.card (Subgroup.centralizer {t2DS}) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
    rw [centralizer_t2DS_eq_P4pS_of_le_normalizer hN6, P4pS,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (P4p_le_Xgrp.trans Xgrp_le_Shat)).toEquiv,
      natCard_P4p]
    norm_num
  exact (Nat.card_congr (centralizerEquiv (MulAut.conj g) t2DS).toEquiv).symm.trans h1

end CFSG.Monster.B.GSide

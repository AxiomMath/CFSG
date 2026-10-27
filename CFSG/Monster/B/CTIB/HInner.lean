module

public import CFSG.Monster.B.CTIB.HInnerReps
public import CFSG.Monster.B.CTIB.Rank2158Final
public import CFSG.Monster.B.CTIB.UniqueComponentAmbient
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
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate16022
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate120
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3013
public import Certificates.Certificate3025
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
public import Certificates.Certificate3059
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
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate16951
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
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

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.E6 CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def rhoAt
    (v : CVert) (ρ : vStab v →* GStar) (s : Sbp) : GStar :=
  open scoped _root_.Classical in if h : sEquiv s ∈ vStab v then ρ ⟨sEquiv s, h⟩ else 1

theorem rank_qS_one :
    ((βr (qS 1)) - 1).rank = 1860 := by
  rw [← rs1_eq]
  exact rank_four.1

theorem rank_xs :
    ((βr xs) - 1).rank = 2048 := by
  rw [← rs0_eq]
  exact rank_four.2.1

theorem isConj_map_sEquiv_iff {a b : Sbp} : IsConj (sEquiv a) (sEquiv b) ↔ IsConj a b := by
  constructor
  · intro h
    have h' := sEquiv.symm.toMonoidHom.map_isConj h
    simpa using h'
  · exact sEquiv.toMonoidHom.map_isConj

theorem clabelS_cv0 :
    clabelS cv0 = cS := Subtype.ext clabel_cv0

theorem isConj_labelS_of_clabelS
    {f : Sbp} {u : CVert} (h : clabelS u = sEquiv f) :
    IsConj f labelS := by
  have h1 := isConj_clabelS u cv0
  rw [h, clabelS_cv0, ← cS_inv, ← sEquiv_labelS] at h1
  exact isConj_map_sEquiv_iff.1 h1

theorem rank_of_clabelS
    {f : Sbp} {u : CVert} (h : clabelS u = sEquiv f) :
    ((βr f) - 1).rank = 1860 := by
  rw [rank_beta_conj ((isConj_labelS_of_clabelS h).trans
    (isConj_of_mem_jClass labelS_mem_jClass)), rank_qS_one]

theorem rank_of_adj
    {s : Sbp} {v u : CVert} (hvu : cgraph.Adj v u)
    (h : sEquiv s = clabelS v * clabelS u) : ((βr s) - 1).rank = 2048 := by
  have h1 := isConj_clabelS_mul_of_adj hvu
  rw [← h, ← sEquiv_xs, isConj_map_sEquiv_iff] at h1
  rw [rank_beta_conj h1, rank_xs]

theorem isConj_rs5_of_dist_three
    {v u : CVert} (h : cgraph.dist v u = 3) :
    IsConj (sEquiv (rs 5)) (clabelS v * clabelS u) := by
  obtain ⟨⟨v₀, u₀, h₀, hc⟩, -⟩ := native_rank_2158_distance_three_product_final
  obtain ⟨s, hs⟩ := cvMul_transitive v₀ v
  have hu₁ : cvMul u₀ s ∈ sphereDistThree v := by
    rw [mem_sphereDistThree, ← hs, dist_cvMul, h₀]
  obtain ⟨g, hgv, hgu⟩ := (distThreePaths_of_ambient ambientRootOrbitsHyp).1 v (cvMul u₀ s) u
    hu₁ (mem_sphereDistThree.2 h)
  refine hc.trans (isConj_iff.2 ⟨(s * g)⁻¹, ?_⟩)
  have ev : clabelS v = (s * g)⁻¹ * clabelS v₀ * (s * g) := by
    rw [← clabelS_cvMul, cvMul_mul, hs, hgv]
  have eu : clabelS u = (s * g)⁻¹ * clabelS u₀ * (s * g) := by
    rw [← clabelS_cvMul, cvMul_mul, hgu]
  rw [ev, eu, inv_inv]
  group

theorem rank_of_dist_three
    {s : Sbp} {v u : CVert} (hvu : cgraph.dist v u = 3)
    (h : sEquiv s = clabelS v * clabelS u) : ((βr s) - 1).rank = 2158 := by
  have h1 := isConj_rs5_of_dist_three hvu
  rw [← h, isConj_map_sEquiv_iff] at h1
  rw [← rank_beta_conj h1]
  exact rank_four.2.2.1

theorem isConj_qS_one_labelS :
    IsConj (qS 1) labelS :=
  (isConj_of_mem_jClass labelS_mem_jClass).symm

theorem existsUnique_clabelS_qS_one :
    ∃! v : CVert, clabelS v = sEquiv (qS 1) := by
  obtain ⟨v, hv⟩ := exists_clabelS_eq ambientRootOrbitsHyp isConj_qS_one_labelS
  refine ⟨v, hv, fun w hw => ?_⟩
  apply (global_label_of_ambient ambientRootOrbitsHyp).1
  rw [← coe_clabelS, ← coe_clabelS, hw, hv]

theorem comm_inv_of {a : Sbp} (ha : a * qS 1 = qS 1 * a) : a⁻¹ * qS 1 = qS 1 * a⁻¹ := by
  calc a⁻¹ * qS 1 = a⁻¹ * (qS 1 * a) * a⁻¹ := by group
    _ = a⁻¹ * (a * qS 1) * a⁻¹ := by rw [ha]
    _ = qS 1 * a⁻¹ := by group

section Local

variable {v : CVert} (hv : clabelS v = sEquiv (qS 1))

include hv

theorem commute_sEquiv_iff {s : Sbp} :
    s * qS 1 = qS 1 * s ↔ ((sEquiv s : Shat) : Dfull) * clabel v = clabel v * sEquiv s := by
  rw [← coe_clabelS, hv, commute_iff_sEquiv]

theorem sEquiv_mem_vStab
    {s : Sbp} (hs : s * qS 1 = qS 1 * s) : sEquiv s ∈ vStab v :=
  ((centralizerInput_of_ambient ambientRootOrbitsHyp) v (sEquiv s)).1
    ((commute_sEquiv_iff hv).1 hs)

theorem commute_of_mem_vStab
    {y : Shat} (hy : y ∈ vStab v) :
    sEquiv.symm y * qS 1 = qS 1 * sEquiv.symm y := by
  rw [commute_sEquiv_iff hv, MulEquiv.apply_symm_apply]
  exact ((centralizerInput_of_ambient ambientRootOrbitsHyp) v y).2 hy

variable {ρ : vStab v →* GStar}

omit hv in
theorem rhoAt_eq
    {s : Sbp} (h : sEquiv s ∈ vStab v) : rhoAt v ρ s = ρ ⟨sEquiv s, h⟩ := by
  open scoped _root_.Classical in rw [rhoAt, dite_eq_left h]

theorem rhoAt_mul
    {a b : Sbp} (ha : a * qS 1 = qS 1 * a) (hb : b * qS 1 = qS 1 * b) :
    rhoAt v ρ (a * b) = rhoAt v ρ a * rhoAt v ρ b := by
  have hab : a * b * qS 1 = qS 1 * (a * b) := comm_mul_of ha hb
  rw [rhoAt_eq (sEquiv_mem_vStab hv hab), rhoAt_eq (sEquiv_mem_vStab hv ha),
    rhoAt_eq (sEquiv_mem_vStab hv hb), ← map_mul]
  congr 1
  exact Subtype.ext (map_mul sEquiv a b)

theorem rhoAt_one :
    rhoAt v ρ 1 = 1 := by
  rw [rhoAt_eq (sEquiv_mem_vStab hv (by rw [one_mul, mul_one]))]
  exact (congrArg ρ (Subtype.ext (map_one sEquiv))).trans (map_one ρ)

theorem rhoAt_inv
    {a : Sbp} (ha : a * qS 1 = qS 1 * a) : rhoAt v ρ a⁻¹ = (rhoAt v ρ a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rhoAt_mul hv (comm_inv_of ha) ha, inv_mul_cancel, rhoAt_one hv]

theorem rhoAt_commute
    {a b : Sbp} (ha : a * qS 1 = qS 1 * a) (hb : b * qS 1 = qS 1 * b)
    (h : Commute a b) : Commute (rhoAt v ρ a) (rhoAt v ρ b) := by
  show rhoAt v ρ a * rhoAt v ρ b = rhoAt v ρ b * rhoAt v ρ a
  rw [← rhoAt_mul hv ha hb, ← rhoAt_mul hv hb ha, h.eq]

theorem rhoAt_eq_one_iff
    (hker : ∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v))
    {a : Sbp} (ha : a * qS 1 = qS 1 * a) : rhoAt v ρ a = 1 ↔ a = 1 ∨ a = qS 1 := by
  rw [rhoAt_eq (sEquiv_mem_vStab hv ha), hker,
    CFSG.Monster.B.Short.mem_zpowers_iff_of_orderOf_eq_two (orderOf_clabel v)]
  have e1 : ((sEquiv a : Shat) : Dfull) = 1 ↔ a = 1 := by
    rw [← Subgroup.coe_one, SetLike.coe_eq_coe, map_eq_one_iff _ sEquiv.injective]
  have e2 : ((sEquiv a : Shat) : Dfull) = clabel v ↔ a = qS 1 := by
    rw [← coe_clabelS, hv, SetLike.coe_eq_coe, sEquiv.injective.eq_iff]
  exact or_congr e1 e2

theorem rhoAt_eq_rhoAt_iff
    (hker : ∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v))
    {a b : Sbp} (ha : a * qS 1 = qS 1 * a) (hb : b * qS 1 = qS 1 * b) :
    rhoAt v ρ a = rhoAt v ρ b ↔ b = a ∨ b = a * qS 1 := by
  have hab : a⁻¹ * b * qS 1 = qS 1 * (a⁻¹ * b) := comm_mul_of (comm_inv_of ha) hb
  rw [← inv_mul_eq_one, ← rhoAt_inv hv ha, ← rhoAt_mul hv (comm_inv_of ha) hb,
    rhoAt_eq_one_iff hv hker hab]
  constructor
  · rintro (h | h)
    · left
      calc b = a * (a⁻¹ * b) := by group
        _ = a := by rw [h, mul_one]
    · right
      calc b = a * (a⁻¹ * b) := by group
        _ = a * qS 1 := by rw [h]
  · rintro (rfl | rfl)
    · left
      group
    · right
      group

variable {iv : cgraph.neighborSet v ≃ rootClass}

theorem rhoAt_of_clabelS
    (hlab : ∀ (z : cgraph.neighborSet v) (y : vStab v), ((y : Shat) : Dfull) = clabel z →
      ρ y = SemidirectProduct.inl (iv z : stdGroup))
    {f : Sbp} (u : cgraph.neighborSet v) (hf : clabelS u = sEquiv f)
    (hfc : f * qS 1 = qS 1 * f) :
    rhoAt v ρ f = SemidirectProduct.inl (iv u : stdGroup) := by
  rw [rhoAt_eq (sEquiv_mem_vStab hv hfc)]
  exact hlab u _ (by rw [← coe_clabelS, hf])

theorem exists_nbr_of_rootType
    {z : Sbp} (hz : z * qS 1 = qS 1 * z) (hsq : z * z = 1)
    (h1 : ((βr z) - 1).rank = 1860) (h2 : ((βr (qS 1 * z)) - 1).rank = 2048) :
    ∃ u : cgraph.neighborSet v, clabelS u = sEquiv z := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [rank_beta_one] at h1
    exact absurd h1 (by decide)
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [sq, hsq]) hz1
  obtain ⟨u, hu⟩ := exists_clabelS_eq ambientRootOrbitsHyp (isConj_labelS_of_rank hord h1)
  have hne : v ≠ u := by
    rintro rfl
    have e : z = qS 1 := sEquiv.injective (hu.symm.trans hv)
    rw [e, qS_one_mul_self, rank_beta_one] at h2
    exact absurd h2 (by decide)
  have hc : Commute (clabelS v) (clabelS u) := by
    rw [hv, hu]
    exact (Commute.map (show Commute (qS 1) z from hz.symm) sEquiv)
  have hprod : sEquiv (qS 1 * z) = clabelS v * clabelS u := by rw [map_mul, hv, hu]
  rcases adj_or_dist_three_of_commute (diameter_three_rank_five_of_ambient ambientRootOrbitsHyp).1
    hne hc with hadj | h3
  · exact ⟨⟨u, hadj⟩, hu⟩
  · rw [rank_of_dist_three h3 hprod] at h2
    exact absurd h2 (by decide)

theorem rhoAt_mem_roots_iff
    (hker : ∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v))
    (hlab : ∀ (z : cgraph.neighborSet v) (y : vStab v), ((y : Shat) : Dfull) = clabel z →
      ρ y = SemidirectProduct.inl (iv z : stdGroup))
    {z : Sbp} (hz : z * qS 1 = qS 1 * z) :
    rhoAt v ρ z ∈ SemidirectProduct.inl '' rootClass ↔ z * z = 1 ∧
      ((((βr z) - 1).rank = 1860 ∧ ((βr (qS 1 * z)) - 1).rank = 2048) ∨
        (((βr z) - 1).rank = 2048 ∧ ((βr (qS 1 * z)) - 1).rank = 1860)) := by
  have hq1z : qS 1 * z * qS 1 = qS 1 * (qS 1 * z) := comm_mul_of rfl hz
  constructor
  · rintro ⟨r, hr, hrz⟩
    set u := iv.symm ⟨r, hr⟩ with hudef
    have hiu : (iv u : stdGroup) = r := by rw [hudef, Equiv.apply_symm_apply]
    set f := sEquiv.symm (clabelS u) with hfdef
    have hf : clabelS u = sEquiv f := by rw [hfdef, MulEquiv.apply_symm_apply]
    have hfc : f * qS 1 = qS 1 * f := by
      have hcomm : Commute (clabelS v) (clabelS u) := commute_clabelS_of_adj u.2
      rw [hv, hf] at hcomm
      have := (Commute.map hcomm sEquiv.symm)
      simp only [MulEquiv.symm_apply_apply] at this
      exact this.eq.symm
    have hrf : rhoAt v ρ f = rhoAt v ρ z := by
      rw [rhoAt_of_clabelS hv hlab u hf hfc, hiu, hrz]
    have hfsq : f * f = 1 := by
      have h := orderOf_clabel u
      have h' : clabelS u * clabelS u = 1 := by
        apply Subtype.ext
        show clabel u * clabel u = 1
        rw [← sq, ← h, pow_orderOf_eq_one]
      rw [hf, ← map_mul, map_eq_one_iff _ sEquiv.injective] at h'
      exact h'
    have hrank : ((βr f) - 1).rank = 1860 := rank_of_clabelS hf
    have hadjr : ((βr (qS 1 * f)) - 1).rank = 2048 :=
      rank_of_adj u.2 (by rw [map_mul, hv, hf])
    rcases (rhoAt_eq_rhoAt_iff hv hker hfc hz).1 hrf with rfl | rfl
    · exact ⟨hfsq, .inl ⟨hrank, hadjr⟩⟩
    · refine ⟨?_, .inr ⟨?_, ?_⟩⟩
      · calc f * qS 1 * (f * qS 1) = f * (qS 1 * f) * qS 1 := by group
          _ = f * (f * qS 1) * qS 1 := by rw [hfc]
          _ = (f * f) * (qS 1 * qS 1) := by group
          _ = 1 := by rw [hfsq, qS_one_mul_self, one_mul]
      · rw [hfc]
        exact hadjr
      · rw [show qS 1 * (f * qS 1) = f by rw [hfc, ← mul_assoc, qS_one_mul_self, one_mul]]
        exact hrank
  · rintro ⟨hsq, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · obtain ⟨u, hu⟩ := exists_nbr_of_rootType hv hz hsq h1 h2
      exact ⟨iv u, (iv u).2, (rhoAt_of_clabelS hv hlab u hu hz).symm⟩
    · have hsq' : qS 1 * z * (qS 1 * z) = 1 := by
        rw [sq_mul_of_comm qS_one_mul_self hz, hsq]
      have h2' : ((βr (qS 1 * (qS 1 * z))) - 1).rank = 2048 := by
        rw [← mul_assoc, qS_one_mul_self, one_mul]
        exact h1
      obtain ⟨u, hu⟩ := exists_nbr_of_rootType hv hq1z hsq' h2 h2'
      refine ⟨iv u, (iv u).2, ?_⟩
      rw [show z = qS 1 * (qS 1 * z) by rw [← mul_assoc, qS_one_mul_self, one_mul],
        rhoAt_mul hv rfl hq1z, (rhoAt_eq_one_iff hv hker rfl).2 (.inr rfl), one_mul,
        rhoAt_of_clabelS hv hlab u hu hq1z]

theorem rank_pair_of_isConj
    (hker : ∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v))
    (hsurj : Function.Surjective ρ) {a b : Sbp} (ha : a * qS 1 = qS 1 * a)
    (hb : b * qS 1 = qS 1 * b) (h : IsConj (rhoAt v ρ a) (rhoAt v ρ b)) :
    (((βr a) - 1).rank = ((βr b) - 1).rank ∧
        ((βr (qS 1 * a)) - 1).rank = ((βr (qS 1 * b)) - 1).rank) ∨
      (((βr a) - 1).rank = ((βr (qS 1 * b)) - 1).rank ∧
        ((βr (qS 1 * a)) - 1).rank = ((βr b) - 1).rank) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  obtain ⟨y, rfl⟩ := hsurj c
  set s := sEquiv.symm (y : Shat) with hsdef
  have hs : s * qS 1 = qS 1 * s := commute_of_mem_vStab hv y.2
  have hys : rhoAt v ρ s = ρ y := by
    rw [rhoAt_eq (sEquiv_mem_vStab hv hs)]
    congr 1
    apply Subtype.ext
    show sEquiv s = (y : Shat)
    rw [hsdef, MulEquiv.apply_symm_apply]
  have hsas : s * a * s⁻¹ * qS 1 = qS 1 * (s * a * s⁻¹) :=
    comm_mul_of (comm_mul_of hs ha) (comm_inv_of hs)
  have hr : rhoAt v ρ (s * a * s⁻¹) = rhoAt v ρ b := by
    rw [rhoAt_mul hv (comm_mul_of hs ha) (comm_inv_of hs), rhoAt_mul hv hs ha,
      rhoAt_inv hv hs, hys, hc]
  have hconj : ∀ t : Sbp, ((βr (s * t * s⁻¹)) - 1).rank = ((βr t) - 1).rank := fun t =>
    rank_beta_conj (isConj_iff.2 ⟨s⁻¹, by group⟩)
  have hq : ∀ t : Sbp, qS 1 * (s * t * s⁻¹) = s * (qS 1 * t) * s⁻¹ := fun t => by
    calc qS 1 * (s * t * s⁻¹) = (qS 1 * s) * t * s⁻¹ := by group
      _ = (s * qS 1) * t * s⁻¹ := by rw [hs]
      _ = s * (qS 1 * t) * s⁻¹ := by group
  rcases (rhoAt_eq_rhoAt_iff hv hker hsas hb).1 hr with hb' | hb'
  · left
    rw [hb', hconj, hq, hconj]
    exact ⟨rfl, rfl⟩
  · right
    have e1 : qS 1 * b = s * a * s⁻¹ := by
      rw [hb', hsas, ← mul_assoc, qS_one_mul_self, one_mul]
    have e2 : b = qS 1 * (s * a * s⁻¹) := by rw [hb', hsas]
    rw [e1, hconj, e2, hq, hconj]
    exact ⟨rfl, rfl⟩

end Local

theorem native_inner_involution_root_products :
    (∃! v : CVert, clabelS v = sEquiv (qS 1)) ∧
    ∀ (v : CVert), clabelS v = sEquiv (qS 1) →
    ∀ (ρ : vStab v →* GStar) (iv : cgraph.neighborSet v ≃ rootClass),
      Function.Surjective ρ →
      (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) →
      (∀ (z : cgraph.neighborSet v) (y : vStab v), ((y : Shat) : Dfull) = clabel z →
        ρ y = SemidirectProduct.inl (iv z : stdGroup)) →
      (∀ s : Sbp, s * qS 1 = qS 1 * s →
        ∃ h : sEquiv s ∈ vStab v, rhoAt v ρ s = ρ ⟨sEquiv s, h⟩) ∧
      (∀ f ∈ [qS 2, qS 4, qS 32, qS 16384, qS 802816], ∃ u : cgraph.neighborSet v,
        clabelS u = sEquiv f ∧ rhoAt v ρ f = SemidirectProduct.inl (iv u : stdGroup)) ∧
      (∃ u : cgraph.neighborSet v, clabelS u = sEquiv (qS 1 * xs) ∧
        rhoAt v ρ xs = SemidirectProduct.inl (iv u : stdGroup) ∧
        rhoAt v ρ (qS 1 * xs) = SemidirectProduct.inl (iv u : stdGroup)) ∧
      (∀ z : Sbp, z * qS 1 = qS 1 * z →
        (rhoAt v ρ z ∈ SemidirectProduct.inl '' rootClass ↔ z * z = 1 ∧
          ((((βr z) - 1).rank = 1860 ∧ ((βr (qS 1 * z)) - 1).rank = 2048) ∨
            (((βr z) - 1).rank = 2048 ∧ ((βr (qS 1 * z)) - 1).rank = 1860)))) ∧
      {z | z ∈ Qs ∧ z * qS 1 = qS 1 * z ∧
        rhoAt v ρ z ∈ SemidirectProduct.inl '' rootClass}.ncard = 3566 ∧
      rhoAt v ρ (qS 2 * qS 4) = rhoAt v ρ (qS 2) * rhoAt v ρ (qS 4) ∧
      rhoAt v ρ (qS 2) ≠ rhoAt v ρ (qS 4) ∧ Commute (rhoAt v ρ (qS 2)) (rhoAt v ρ (qS 4)) ∧
      rhoAt v ρ (qS 2 * qS 4) ∉ SemidirectProduct.inl '' rootClass ∧
      rhoAt v ρ (qS 32 * qS 16384 * qS 802816) =
        rhoAt v ρ (qS 32) * rhoAt v ρ (qS 16384) * rhoAt v ρ (qS 802816) ∧
      rhoAt v ρ (qS 32) ≠ rhoAt v ρ (qS 16384) ∧ rhoAt v ρ (qS 32) ≠ rhoAt v ρ (qS 802816) ∧
      rhoAt v ρ (qS 16384) ≠ rhoAt v ρ (qS 802816) ∧
      Commute (rhoAt v ρ (qS 32)) (rhoAt v ρ (qS 16384)) ∧
      Commute (rhoAt v ρ (qS 32)) (rhoAt v ρ (qS 802816)) ∧
      Commute (rhoAt v ρ (qS 16384)) (rhoAt v ρ (qS 802816)) ∧
      rhoAt v ρ (qS 32) * rhoAt v ρ (qS 16384) ∉ SemidirectProduct.inl '' rootClass ∧
      rhoAt v ρ (qS 32) * rhoAt v ρ (qS 802816) ∉ SemidirectProduct.inl '' rootClass ∧
      rhoAt v ρ (qS 16384) * rhoAt v ρ (qS 802816) ∉ SemidirectProduct.inl '' rootClass ∧
      rhoAt v ρ (qS 32 * qS 16384 * qS 802816) ∉ SemidirectProduct.inl '' rootClass ∧
      ¬ IsConj (rhoAt v ρ xs) (rhoAt v ρ (qS 2 * qS 4)) ∧
      ¬ IsConj (rhoAt v ρ xs) (rhoAt v ρ (qS 32 * qS 16384 * qS 802816)) ∧
      ¬ IsConj (rhoAt v ρ (qS 2 * qS 4)) (rhoAt v ρ (qS 32 * qS 16384 * qS 802816)) := by
  refine ⟨existsUnique_clabelS_qS_one, fun v hv ρ iv hsurj hker hlab => ?_⟩
  have hroots := fun z hz => rhoAt_mem_roots_iff (iv := iv) hv hker hlab (z := z) hz
  obtain ⟨hR, hC2, hC3, hC4, hC5, hO, hX, -, -, hY3e, hY3, -⟩ :=
    native_inner_involution_representatives
  have hc := fun f hf => (hR f hf).2.1
  have hf2 := hR (qS 2) (by simp)
  have hf4 := hR (qS 4) (by simp)
  have hf32 := hR (qS 32) (by simp)
  have hf16 := hR (qS 16384) (by simp)
  have hf80 := hR (qS 802816) (by simp)
  have hfac : ∀ f ∈ [qS 2, qS 4, qS 32, qS 16384, qS 802816], ∃ u : cgraph.neighborSet v,
      clabelS u = sEquiv f ∧ rhoAt v ρ f = SemidirectProduct.inl (iv u : stdGroup) := by
    intro f hf
    obtain ⟨-, hfc, hsq, h1, h2⟩ := hR f hf
    obtain ⟨u, hu⟩ := exists_nbr_of_rootType hv hfc hsq h1 h2
    exact ⟨u, hu, rhoAt_of_clabelS hv hlab u hu hfc⟩
  have hxroot : ∃ u : cgraph.neighborSet v, clabelS u = sEquiv (qS 1 * xs) ∧
      rhoAt v ρ xs = SemidirectProduct.inl (iv u : stdGroup) ∧
      rhoAt v ρ (qS 1 * xs) = SemidirectProduct.inl (iv u : stdGroup) := by
    obtain ⟨-, hxc, -, hx1, hx2⟩ := hX
    have hq1x : qS 1 * xs * qS 1 = qS 1 * (qS 1 * xs) := comm_mul_of rfl hxc
    have hsq : qS 1 * xs * (qS 1 * xs) = 1 := by
      rw [sq_mul_of_comm qS_one_mul_self hxc, xs_mul_self]
    have h2' : ((βr (qS 1 * (qS 1 * xs))) - 1).rank = 2048 := by
      rw [← mul_assoc, qS_one_mul_self, one_mul]
      exact hx1
    obtain ⟨u, hu⟩ := exists_nbr_of_rootType hv hq1x hsq hx2 h2'
    have hr := rhoAt_of_clabelS hv hlab u hu hq1x
    refine ⟨u, hu, ?_, hr⟩
    rw [show xs = qS 1 * (qS 1 * xs) by rw [← mul_assoc, qS_one_mul_self, one_mul],
      rhoAt_mul hv rfl hq1x, (rhoAt_eq_one_iff hv hker rfl).2 (.inr rfl), one_mul, hr]
  have hnot : ∀ p : Sbp, InnerType (qS 1) 2048 2168 p →
      rhoAt v ρ p ∉ SemidirectProduct.inl '' rootClass := by
    intro p hp hmem
    obtain ⟨-, hpc, -, hp1, hp2⟩ := hp
    obtain ⟨-, h | h⟩ := (hroots p hpc).1 hmem
    · rw [hp1] at h
      exact absurd h.1 (by decide)
    · rw [hp2] at h
      exact absurd h.2 (by decide)
  have hnot3 : rhoAt v ρ (qS 32 * qS 16384 * qS 802816) ∉ SemidirectProduct.inl '' rootClass := by
    intro hmem
    rw [hY3e] at hmem
    obtain ⟨-, hpc, -, hp1, -⟩ := hY3
    obtain ⟨-, h | h⟩ := (hroots _ hpc).1 hmem
    · rw [hp1] at h
      exact absurd h.1 (by decide)
    · rw [hp1] at h
      exact absurd h.1 (by decide)
  have hdist : ∀ a b : Sbp, InnerType (qS 1) 1860 2048 a → b * qS 1 = qS 1 * b →
      InnerType (qS 1) 2048 2168 (a * b) → rhoAt v ρ a ≠ rhoAt v ρ b := by
    intro a b ha hb hab he
    obtain ⟨-, hac, haa, -, -⟩ := ha
    obtain ⟨-, -, -, h1, -⟩ := hab
    rcases (rhoAt_eq_rhoAt_iff hv hker hac hb).1 he with rfl | rfl
    · rw [haa, rank_beta_one] at h1
      exact absurd h1 (by decide)
    · rw [← mul_assoc, haa, one_mul, rank_qS_one] at h1
      exact absurd h1 (by decide)
  have hcount : {z | z ∈ Qs ∧ z * qS 1 = qS 1 * z ∧
      rhoAt v ρ z ∈ SemidirectProduct.inl '' rootClass}.ncard = 3566 := by
    obtain ⟨-, -, h3, h4, -⟩ := census_q1
    have e : {z | z ∈ Qs ∧ z * qS 1 = qS 1 * z ∧
        rhoAt v ρ z ∈ SemidirectProduct.inl '' rootClass} =
        {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 1860 ∧
          ((βr (qS 1 * y)) - 1).rank = 2048)} ∪
        {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 2048 ∧
          ((βr (qS 1 * y)) - 1).rank = 1860)} := by
      ext z
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hz, hzc, hm⟩
        obtain ⟨hsq, h | h⟩ := (hroots z hzc).1 hm
        · exact .inl ⟨hz, hzc, hsq, h⟩
        · exact .inr ⟨hz, hzc, hsq, h⟩
      · rintro (⟨hz, hzc, hsq, h⟩ | ⟨hz, hzc, hsq, h⟩)
        · exact ⟨hz, hzc, (hroots z hzc).2 ⟨hsq, .inl h⟩⟩
        · exact ⟨hz, hzc, (hroots z hzc).2 ⟨hsq, .inr h⟩⟩
    have hdisj : Disjoint
        {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 1860 ∧
          ((βr (qS 1 * y)) - 1).rank = 2048)}
        {y | y ∈ Qs ∧ y * qS 1 = qS 1 * y ∧ (y * y = 1 ∧ ((βr y) - 1).rank = 2048 ∧
          ((βr (qS 1 * y)) - 1).rank = 1860)} := by
      rw [Set.disjoint_left]
      rintro z ⟨-, -, -, h1, -⟩ ⟨-, -, -, h2, -⟩
      rw [h1] at h2
      exact absurd h2 (by decide)
    rw [e, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), h4, h3]
  have hO2 := hO _ (show qS 2 * qS 4 ∈ [qS 2 * qS 4, qS 32 * qS 16384, qS 32 * qS 802816,
    qS 16384 * qS 802816] by simp)
  have hO34 := hO _ (show qS 32 * qS 16384 ∈ [qS 2 * qS 4, qS 32 * qS 16384,
    qS 32 * qS 802816, qS 16384 * qS 802816] by simp)
  have hO35 := hO _ (show qS 32 * qS 802816 ∈ [qS 2 * qS 4, qS 32 * qS 16384,
    qS 32 * qS 802816, qS 16384 * qS 802816] by simp)
  have hO45 := hO _ (show qS 16384 * qS 802816 ∈ [qS 2 * qS 4, qS 32 * qS 16384,
    qS 32 * qS 802816, qS 16384 * qS 802816] by simp)
  have hy3c : qS 32 * qS 16384 * qS 802816 * qS 1 = qS 1 * (qS 32 * qS 16384 * qS 802816) :=
    comm_mul_of (comm_mul_of hf32.2.1 hf16.2.1) hf80.2.1
  refine ⟨fun s hs => ⟨sEquiv_mem_vStab hv hs, rhoAt_eq _⟩, hfac, hxroot, fun z hz => hroots z hz,
    hcount, rhoAt_mul hv hf2.2.1 hf4.2.1,
    hdist _ _ hf2 hf4.2.1 hO2, rhoAt_commute hv hf2.2.1 hf4.2.1 hC2, hnot _ hO2, ?_,
    hdist _ _ hf32 hf16.2.1 hO34, hdist _ _ hf32 hf80.2.1 hO35, hdist _ _ hf16 hf80.2.1 hO45,
    rhoAt_commute hv hf32.2.1 hf16.2.1 hC3, rhoAt_commute hv hf32.2.1 hf80.2.1 hC4,
    rhoAt_commute hv hf16.2.1 hf80.2.1 hC5, ?_, ?_, ?_, hnot3, ?_, ?_, ?_⟩
  · rw [rhoAt_mul hv (comm_mul_of hf32.2.1 hf16.2.1) hf80.2.1, rhoAt_mul hv hf32.2.1 hf16.2.1]
  · rw [← rhoAt_mul hv hf32.2.1 hf16.2.1]
    exact hnot _ hO34
  · rw [← rhoAt_mul hv hf32.2.1 hf80.2.1]
    exact hnot _ hO35
  · rw [← rhoAt_mul hv hf16.2.1 hf80.2.1]
    exact hnot _ hO45
  · intro h
    rcases rank_pair_of_isConj hv hker hsurj hX.2.1 hO2.2.1 h with ⟨-, h2⟩ | ⟨h1, -⟩
    · rw [hX.2.2.2.2, hO2.2.2.2.2] at h2
      exact absurd h2 (by decide)
    · rw [hX.2.2.2.1, hO2.2.2.2.2] at h1
      exact absurd h1 (by decide)
  · intro h
    rw [hY3e] at h
    rcases rank_pair_of_isConj hv hker hsurj hX.2.1 hY3.2.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [hX.2.2.2.1, hY3.2.2.2.1] at h1
      exact absurd h1 (by decide)
    · rw [hX.2.2.2.1, hY3.2.2.2.2] at h1
      exact absurd h1 (by decide)
  · intro h
    rw [hY3e] at h
    rcases rank_pair_of_isConj hv hker hsurj hO2.2.1 hY3.2.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [hO2.2.2.2.1, hY3.2.2.2.1] at h1
      exact absurd h1 (by decide)
    · rw [hO2.2.2.2.1, hY3.2.2.2.2] at h1
      exact absurd h1 (by decide)

end CFSG.Monster.B.CTIB

module

public import CFSG.Monster.B.GSide.CompletionFusion
public import CFSG.Monster.B.CTIB.HOuter
public import CFSG.LocalAnalysis.ZStar
public import CFSG.Monster.B.CTIB.OddCoreFree
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
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.CTIB

theorem rankS_sq_of_orderOf_four
    {p q : CVert} (h : orderOf (clabelS p * clabelS q) = 4) :
    rankS ((clabelS p * clabelS q) ^ 2) = 2048 := by
  rcases commute_or_three_or_four (diameter_three_rank_five_of_ambient ambientRootOrbitsHyp).1
      (labelsInput_of_ambient ambientRootOrbitsHyp) p q with hc | ⟨-, h3⟩ | ⟨hq, -⟩
  · have h2 := orderOf_dvd_of_pow_eq_one (sq_clabelS_mul_of_commute hc)
    rw [h] at h2
    exact absurd h2 (by decide)
  · rw [h] at h3
    exact absurd h3 (by decide)
  · obtain ⟨s, hp, hqs⟩ := (native_coset_graph_order_four_common_neighbors.1 p q hq).2.2.1
    have hsq := sq_clabel_mul_of_mem_cPi hq hp hqs
    have e : (clabelS p * clabelS q) ^ 2 = s⁻¹ * xhatS * s := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, coe_clabelS]
      exact hsq
    have hc : IsConj xhatS (s⁻¹ * xhatS * s) := isConj_iff.2 ⟨s⁻¹, by group⟩
    rw [e, ← rankS_conj hc, ← sEquiv_xs]
    exact rankS_sEquiv_xs

theorem rankS_cV0_mul_clabelS
    {u : CVert} (hu : u ∈ sphereDistThree cv0) :
    rankS ((cV0 : Shat) * clabelS u) = 2158 := by
  rw [coe_cV0]
  exact rank_clabelS_mul_of_dist_three hu

theorem eq_or_eq_of_isConj_cV0
    {u : CVert} (hu : u ∈ sphereDistThree cv0) {a : Shat}
    (ha : IsConj (cV0 : Shat) a) (hta : IsConj (cV0 : Shat) ((cV0 : Shat) * clabelS u * a)) :
    a = cV0 ∨ a = clabelS u := by
  have h := (distance_three_product_determines_endpoints_final hu).1
  rw [← coe_cV0] at h
  have hmem : a ∈ {a : Shat | IsConj (cV0 : Shat) a ∧
      IsConj (cV0 : Shat) ((cV0 : Shat) * clabelS u * a)} := ⟨ha, hta⟩
  rw [h] at hmem
  exact hmem

section Completion

variable {G : Type*} [Group G] {d : G} (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
  {Φ : Shat →* G} (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)

include hd hΦ in
theorem exists_eq_map_of_mem_dZero
    {x : G} (hx : x ∈ dZero Φ.range d) :
    ∃ a : Shat, IsConj (cV0 : Shat) a ∧ Φ a = x := by
  obtain ⟨_, ⟨g, rfl⟩, rfl⟩ := hx
  refine ⟨g * cV0 * g⁻¹, isConj_iff.2 ⟨g, rfl⟩, ?_⟩
  rw [map_mul, map_mul, map_inv, map_cV0_of_psiInvHom hd ψ hΦ]

theorem mem_dZero_of_isConj
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) {x : G} (hx : x ∈ Φ.range)
    (hdx : IsConj d x) : x ∈ dZero Φ.range d :=
  hDM ▸ (⟨hdx, hx⟩ : x ∈ conjugatesOf d ∩ (Φ.range : Set G))

include hd hΦ in
theorem isConj_map_of_isConj_cV0
    {a : Shat} (ha : IsConj (cV0 : Shat) a) : IsConj d (Φ a) := by
  have h := Φ.map_isConj ha
  rwa [map_cV0_of_psiInvHom hd ψ hΦ] at h

end Completion

section Generic

variable {S G : Type*} [Group S] [Group G] {Φ : S →* G} (hinj : Function.Injective Φ)
  {c e : S} {d : G} (hc : Φ c = d) (hc2 : c * c = 1) (hce : c * e = e * c)

include hc hc2 hce in
theorem commute_mul_gen : d * Φ (c * e) = Φ (c * e) * d ∧ d * Φ (c * e) = Φ e := by
  have hct : c * (c * e) = c * e * c := by rw [mul_assoc c e c, ← hce]
  refine ⟨by rw [← hc, ← map_mul, ← map_mul, hct], ?_⟩
  rw [← hc, ← map_mul, ← mul_assoc, hc2, one_mul]

theorem conj_commute_gen {d t g : G} (hdt : d * t = t * d) (hg : g * t = t * g) :
    g * d * g⁻¹ * t = t * (g * d * g⁻¹) ∧ g * d * g⁻¹ * t = g * (d * t) * g⁻¹ := by
  have h1 : g⁻¹ * t * g = t := by rw [mul_assoc, ← hg, inv_mul_cancel_left]
  have h2 : g * d * g⁻¹ * t = g * (d * t) * g⁻¹ := by
    calc g * d * g⁻¹ * t = g * d * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = g * (d * t) * g⁻¹ := by rw [h1]; group
  refine ⟨?_, h2⟩
  rw [h2, hdt]
  calc g * (t * d) * g⁻¹ = (g * t) * d * g⁻¹ := by group
    _ = t * (g * d * g⁻¹) := by rw [hg]; group

include hinj hc hc2 hce in
theorem eq_or_eq_of_commute_gen (hCd : Subgroup.centralizer {d} ≤ Φ.range)
    (hD : ∀ x ∈ Φ.range, IsConj d x → ∃ a : S, IsConj c a ∧ Φ a = x) (hE : IsConj c e)
    (hend : ∀ a : S, IsConj c a → IsConj c (c * e * a) → a = c ∨ a = e) {g : G}
    (hg : g * Φ (c * e) = Φ (c * e) * g) (hx : g * d * g⁻¹ * d = d * (g * d * g⁻¹)) :
    g * d * g⁻¹ = d ∨ g * d * g⁻¹ = Φ e := by
  obtain ⟨hdt, hde⟩ := commute_mul_gen hc hc2 hce
  obtain ⟨hxt, hxt'⟩ := conj_commute_gen hdt hg
  obtain ⟨a, ha, hax⟩ := hD _ (hCd (Subgroup.mem_centralizer_singleton_iff.2 hx))
    (isConj_iff.2 ⟨g, rfl⟩)
  have hEd : IsConj d (g * d * g⁻¹ * Φ (c * e)) := by
    rw [hxt', hde]
    have h := Φ.map_isConj hE
    rw [hc] at h
    exact h.trans (isConj_iff.2 ⟨g, rfl⟩)
  have hmem : g * d * g⁻¹ * Φ (c * e) ∈ Φ.range :=
    ⟨a * (c * e), by rw [map_mul Φ a (c * e), hax]⟩
  obtain ⟨b, hb, hbx⟩ := hD _ hmem hEd
  have hab : b = a * (c * e) := hinj (by rw [hbx, map_mul Φ a (c * e), hax])
  have hcomm : a * (c * e) = c * e * a := hinj (by
    rw [map_mul Φ a (c * e), map_mul Φ (c * e) a, hax, hxt])
  have hb' : IsConj c (c * e * a) := by
    rw [← hcomm, ← hab]
    exact hb
  rcases hend a ha hb' with h | h
  · left
    rw [← hax, h, hc]
  · right
    rw [← hax, h]

theorem map_conj_closure_pair_le_gen {p q y : G} (hp : y * p * y⁻¹ = q) (hq : y * q * y⁻¹ = p) :
    (Subgroup.closure {p, q}).map (MulAut.conj y).toMonoidHom ≤ Subgroup.closure {p, q} := by
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨z, hz, rfl⟩
  rcases hz with rfl | rfl
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hp]
    exact Subgroup.subset_closure (by simp)
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hq]
    exact Subgroup.subset_closure (by simp)

theorem mem_normalizer_closure_pair_gen {p q y : G} (hp : y * p * y⁻¹ = q)
    (hq : y * q * y⁻¹ = p) :
    y ∈ Subgroup.normalizer (Subgroup.closure {p, q} : Set G) := by
  have hle := map_conj_closure_pair_le_gen hp hq
  have hp' : y⁻¹ * q * y⁻¹⁻¹ = p := by rw [← hp]; group
  have hq' : y⁻¹ * p * y⁻¹⁻¹ = q := by rw [← hq]; group
  have hle' := map_conj_closure_pair_le_gen hq' hp'
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hle ⟨h, hh, rfl⟩
  · intro hh
    have h2 := hle' ⟨_, hh, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h by group] at h2

include hinj hc hc2 hce in
theorem false_of_anticommute_gen (he2 : e * e = 1)
    (hD : ∀ x ∈ Φ.range, IsConj d x → ∃ a : S, IsConj c a ∧ Φ a = x)
    (hN : Subgroup.normalizer (Subgroup.closure {d, Φ e} : Set G) ≤ Φ.range)
    (hsq : ∀ a : S, IsConj c a → (a * c) ^ 2 ≠ c * e) {g : G}
    (hg : g * Φ (c * e) = Φ (c * e) * g)
    (hx : g * d * g⁻¹ * d = d * (g * d * g⁻¹) * Φ (c * e)) : False := by
  obtain ⟨hdt, hde⟩ := commute_mul_gen hc hc2 hce
  obtain ⟨hxt, -⟩ := conj_commute_gen hdt hg
  have hd2 : d * d = 1 := by rw [← hc, ← map_mul, hc2, map_one]
  have hce2 : c * e * (c * e) = 1 := by
    calc c * e * (c * e) = c * (e * c) * e := by group
      _ = c * (c * e) * e := by rw [hce]
      _ = (c * c) * (e * e) := by group
      _ = 1 := by rw [hc2, he2, one_mul]
  have ht2 : Φ (c * e) * Φ (c * e) = 1 := by rw [← map_mul, hce2, map_one]
  have htinv : (Φ (c * e))⁻¹ = Φ (c * e) := inv_eq_of_mul_eq_one_left ht2
  have hx2 : g * d * g⁻¹ * (g * d * g⁻¹) = 1 := by
    calc g * d * g⁻¹ * (g * d * g⁻¹) = g * (d * d) * g⁻¹ := by group
      _ = 1 := by rw [hd2, mul_one, mul_inv_cancel]
  have hxinv : (g * d * g⁻¹)⁻¹ = g * d * g⁻¹ := inv_eq_of_mul_eq_one_left hx2
  have hxtx : g * d * g⁻¹ * Φ (c * e) * (g * d * g⁻¹)⁻¹ = Φ (c * e) := by
    rw [hxt, mul_inv_cancel_right]
  have h1 : g * d * g⁻¹ * d * (g * d * g⁻¹)⁻¹ = Φ e := by
    calc g * d * g⁻¹ * d * (g * d * g⁻¹)⁻¹ =
        d * (g * d * g⁻¹) * Φ (c * e) * (g * d * g⁻¹)⁻¹ := by rw [hx]
      _ = d * (g * d * g⁻¹ * Φ (c * e) * (g * d * g⁻¹)⁻¹) := by group
      _ = Φ e := by rw [hxtx, hde]
  have h2 : g * d * g⁻¹ * Φ e * (g * d * g⁻¹)⁻¹ = d := by
    calc g * d * g⁻¹ * Φ e * (g * d * g⁻¹)⁻¹ =
        g * d * g⁻¹ * (d * Φ (c * e)) * (g * d * g⁻¹)⁻¹ := by rw [hde]
      _ = (g * d * g⁻¹ * d * (g * d * g⁻¹)⁻¹) *
          (g * d * g⁻¹ * Φ (c * e) * (g * d * g⁻¹)⁻¹) := by group
      _ = d * Φ (c * e) * Φ (c * e) := by rw [h1, hxtx, ← hde]
      _ = d := by rw [mul_assoc, ht2, mul_one]
  have hnorm := mem_normalizer_closure_pair_gen h1 h2
  obtain ⟨a, ha, hax⟩ := hD _ (hN hnorm) (isConj_iff.2 ⟨g, rfl⟩)
  have hsq' : (g * d * g⁻¹ * d) ^ 2 = Φ (c * e) := by
    calc (g * d * g⁻¹ * d) ^ 2 = g * d * g⁻¹ * d * (g * d * g⁻¹ * d) := sq _
      _ = d * (g * d * g⁻¹) * Φ (c * e) * (g * d * g⁻¹ * d) := by rw [hx]
      _ = d * (g * d * g⁻¹ * Φ (c * e) * (g * d * g⁻¹)) * d := by group
      _ = d * (Φ (c * e) * (g * d * g⁻¹ * (g * d * g⁻¹))) * d := by rw [hxt]; group
      _ = d * Φ (c * e) * d := by rw [hx2, mul_one]
      _ = Φ (c * e) := by rw [hdt, mul_assoc, hd2, mul_one]
  exact hsq a ha (hinj (by rw [map_pow, map_mul Φ a c, hax, hc, hsq']))

instance zpowers_normal_centralizer {G : Type*} [Group G] (t : G) :
    (Subgroup.zpowers (⟨t, mem_centralizer_singleton_self t⟩ :
      Subgroup.centralizer {t})).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  have hg : g * (⟨t, mem_centralizer_singleton_self t⟩ : Subgroup.centralizer {t}) =
      ⟨t, mem_centralizer_singleton_self t⟩ * g :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  rw [(Commute.zpow_right hg k).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers _ k

theorem conj_eq_or_eq_of_zStar {G : Type} [Group G] [Finite G] {d t : G} (hd1 : d ≠ 1)
    (hd2 : d * d = 1) (ht1 : t ≠ 1) (ht2 : t * t = 1) (hdt : d * t = t * d) (hdt1 : d ≠ t)
    (hiso1 : ∀ g ∈ Subgroup.centralizer {t}, g * d * g⁻¹ * d = d * (g * d * g⁻¹) →
      g * d * g⁻¹ = d ∨ g * d * g⁻¹ = d * t)
    (hiso2 : ∀ g ∈ Subgroup.centralizer {t}, g * d * g⁻¹ * d ≠ d * (g * d * g⁻¹) * t)
    (hObar : ∀ N : Subgroup (Subgroup.centralizer {t} ⧸ Subgroup.zpowers
      (⟨t, mem_centralizer_singleton_self t⟩ : Subgroup.centralizer {t})),
      N.Normal → Odd (Nat.card N) → N = ⊥) :
    ∀ g ∈ Subgroup.centralizer {t}, g * d * g⁻¹ = d ∨ g * d * g⁻¹ = d * t := by
  set C := Subgroup.centralizer {t}
  set tC : C := ⟨t, mem_centralizer_singleton_self t⟩
  set Z := Subgroup.zpowers tC
  have hZ : Z.Normal := zpowers_normal_centralizer t
  have hdC : d ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hdt
  set dC : C := ⟨d, hdC⟩
  have htC2 : orderOf tC = 2 := by
    refine orderOf_eq_prime (by rw [sq]; exact Subtype.ext ht2) (fun h => ht1 ?_)
    exact congrArg Subtype.val h
  have hmemZ : ∀ x : C, x ∈ Z ↔ x = 1 ∨ x = tC := fun x =>
    Short.mem_zpowers_iff_of_orderOf_eq_two htC2
  have : Fintype (C ⧸ Z) := Fintype.ofFinite _
  have ha1 : (dC : C ⧸ Z) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, hmemZ]
    rintro (h | h)
    · exact hd1 (congrArg Subtype.val h)
    · exact hdt1 (congrArg Subtype.val h)
  have ha2 : (dC : C ⧸ Z) * (dC : C ⧸ Z) = 1 := by
    rw [← QuotientGroup.mk_mul, show dC * dC = 1 from Subtype.ext hd2, QuotientGroup.mk_one]
  have hiso : ∀ q : C ⧸ Z, q * (dC : C ⧸ Z) * q⁻¹ * (dC : C ⧸ Z) =
      (dC : C ⧸ Z) * (q * (dC : C ⧸ Z) * q⁻¹) → q * (dC : C ⧸ Z) * q⁻¹ = (dC : C ⧸ Z) := by
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv] at hq ⊢
    rw [QuotientGroup.eq, hmemZ] at hq
    rw [QuotientGroup.eq, hmemZ]
    rcases hq with h | h
    · have hc : (g : G) * d * (g : G)⁻¹ * d = d * ((g : G) * d * (g : G)⁻¹) := by
        have := congrArg Subtype.val (inv_mul_eq_one.1 h)
        simpa using this
      rcases hiso1 g g.2 hc with h' | h'
      · left
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
        rw [h', inv_mul_cancel]
      · right
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [h']
        show (d * t)⁻¹ * d = t
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact inv_eq_of_mul_eq_one_left ht2
    · exfalso
      apply hiso2 g g.2
      have h' : dC * (g * dC * g⁻¹) = g * dC * g⁻¹ * dC * tC := by rw [← h]; group
      have h'' : d * ((g : G) * d * (g : G)⁻¹) = (g : G) * d * (g : G)⁻¹ * d * t := by
        have := congrArg Subtype.val h'
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
      calc (g : G) * d * (g : G)⁻¹ * d = ((g : G) * d * (g : G)⁻¹ * d * t) * t := by
            rw [mul_assoc _ t t, ht2, mul_one]
        _ = d * ((g : G) * d * (g : G)⁻¹) * t := by rw [← h'']
  obtain ⟨N, hN, hNodd, hNmem⟩ := CFSG.ZStar.glauberman_zStar (C ⧸ Z) (dC : C ⧸ Z) ha1 ha2 hiso
  have hNbot := hObar N hN hNodd
  intro g hg
  have hmem := hNmem (⟨g, hg⟩ : C)
  rw [hNbot, Subgroup.mem_bot] at hmem
  simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv] at hmem
  rw [QuotientGroup.eq_one_iff, hmemZ] at hmem
  rcases hmem with h | h
  · left
    have := congrArg Subtype.val (mul_inv_eq_one.1 h)
    simpa using this
  · right
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
    calc g * d * g⁻¹ = g * d * g⁻¹ * d⁻¹ * d := by group
      _ = t * d := by rw [h']
      _ = d * t := hdt.symm

end Generic

theorem sq_ne_of_isConj_cV0
    {u : CVert} (hu : u ∈ sphereDistThree cv0) {a : Shat}
    (ha : IsConj (cV0 : Shat) a) : (a * (cV0 : Shat)) ^ 2 ≠ (cV0 : Shat) * clabelS u := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha' : IsConj (clabelS cv0) a := by rwa [← coe_cV0]
  obtain ⟨p, hp⟩ := exists_clabelS_eq_of_isConj ha'
  subst hp
  have h2 := orderOf_cV0_mul_clabelS hu
  have h4 : orderOf (clabelS p * clabelS cv0) = 4 := by
    rw [← coe_cV0]
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · rw [pow_one, h]
      intro h1
      rw [h1, orderOf_one] at h2
      exact absurd h2 (by decide)
    · rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, h, ← h2, pow_orderOf_eq_one]
  have hr := rankS_sq_of_orderOf_four h4
  rw [← coe_cV0, h, rankS_cV0_mul_clabelS hu] at hr
  exact absurd hr (by decide)

theorem centralizer_le_range_of_twoC_quot
    {G : Type} [Group G] [Finite G] {d : G} (hd : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) {u : CVert}
    (hu : u ∈ sphereDistThree cv0)
    (hObar : ∀ N : Subgroup (Subgroup.centralizer {Φ ((cV0 : Shat) * clabelS u)} ⧸
      Subgroup.zpowers (⟨Φ ((cV0 : Shat) * clabelS u), mem_centralizer_singleton_self _⟩ :
        Subgroup.centralizer {Φ ((cV0 : Shat) * clabelS u)})),
      N.Normal → Odd (Nat.card N) → N = ⊥) :
    Subgroup.centralizer {Φ ((cV0 : Shat) * clabelS u)} ≤ Φ.range := by
  have hΦc : Φ (cV0 : Shat) = d := map_cV0_of_psiInvHom hd ψ hΦ
  have hinj : Function.Injective Φ := injective_of_map_cV0_ne_one Φ (hΦc.symm ▸ hd)
  have hC := completion_centralizer hd ψ Φ hΦ
  have hc2 : (cV0 : Shat) * cV0 = 1 := cV0_mul_self_coe
  have hce := cV0_mul_clabelS_comm hu
  have he2 : clabelS u * clabelS u = 1 := clabelS_mul_clabelS u
  have hE : IsConj (cV0 : Shat) (clabelS u) := by
    rw [coe_cV0]
    exact isConj_clabelS cv0 u
  have hD : ∀ x ∈ Φ.range, IsConj d x → ∃ a : Shat, IsConj (cV0 : Shat) a ∧ Φ a = x :=
    fun x hx hdx => exists_eq_map_of_mem_dZero hd ψ hΦ (mem_dZero_of_isConj hDM hx hdx)
  have hN : Subgroup.normalizer (Subgroup.closure {d, Φ (clabelS u)} : Set G) ≤ Φ.range :=
    normalizer_le_of_mem_dZero hC.2.2 (fun x hx hdx => mem_dZero_of_isConj hDM hx hdx)
      (by
        rw [Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact ⟨_, hΦc⟩
        · exact ⟨_, rfl⟩)
      ⟨d, Subgroup.subset_closure (by simp), self_mem_dZero _ d⟩
  obtain ⟨hdt, hde⟩ := commute_mul_gen hΦc hc2 hce
  have hd2 : d * d = 1 := by rw [← hΦc, ← map_mul, hc2, map_one]
  have hce1 : (cV0 : Shat) * clabelS u ≠ 1 := fun h => by
    have h2 := orderOf_cV0_mul_clabelS hu
    rw [h, orderOf_one] at h2
    exact absurd h2 (by decide)
  have ht1 : Φ ((cV0 : Shat) * clabelS u) ≠ 1 := fun h => hce1 (hinj (h.trans (map_one Φ).symm))
  have ht2 : Φ ((cV0 : Shat) * clabelS u) * Φ ((cV0 : Shat) * clabelS u) = 1 := by
    rw [← map_mul, show (cV0 : Shat) * clabelS u * ((cV0 : Shat) * clabelS u) =
      ((cV0 : Shat) * cV0) * (clabelS u * clabelS u) by
        rw [mul_assoc, ← mul_assoc (clabelS u), ← hce, mul_assoc, mul_assoc], hc2, he2,
      one_mul, map_one]
  have hdt1 : d ≠ Φ ((cV0 : Shat) * clabelS u) := fun h => by
    have h1 : (cV0 : Shat) = cV0 * clabelS u := hinj (hΦc.trans h)
    have h2 : clabelS u = 1 := by
      have := congrArg (fun x => (cV0 : Shat)⁻¹ * x) h1
      simpa using this.symm
    rw [h2, mul_one] at he2
    exact absurd he2 (by
      intro h3
      have := orderOf_clabelS u
      rw [← Subgroup.orderOf_coe, h2] at this
      simp at this)
  have hconj := conj_eq_or_eq_of_zStar hd hd2 ht1 ht2 hdt hdt1
    (fun g hg hx => by
      rw [hde]
      exact eq_or_eq_of_commute_gen hinj hΦc hc2 hce hC.2.1 hD hE
        (fun a ha hb => eq_or_eq_of_isConj_cV0 hu ha hb)
        (Subgroup.mem_centralizer_singleton_iff.1 hg) hx)
    (fun g hg hx => false_of_anticommute_gen hinj hΦc hc2 hce he2 hD hN
      (fun a ha => sq_ne_of_isConj_cV0 hu ha) (Subgroup.mem_centralizer_singleton_iff.1 hg) hx)
    hObar
  intro g hg
  rcases hconj g hg with h | h
  · refine hC.2.1 (Subgroup.mem_centralizer_singleton_iff.2 ?_)
    calc g * d = g * d * g⁻¹ * g := by group
      _ = d * g := by rw [h]
  · rw [hde] at h
    refine hN (mem_normalizer_closure_pair_gen h ?_)
    have hg' := Subgroup.mem_centralizer_singleton_iff.1 hg
    rw [← hde]
    calc g * (d * Φ ((cV0 : Shat) * clabelS u)) * g⁻¹ =
        (g * d * g⁻¹) * (g * Φ ((cV0 : Shat) * clabelS u) * g⁻¹) := by group
      _ = d * Φ ((cV0 : Shat) * clabelS u) * Φ ((cV0 : Shat) * clabelS u) := by
          rw [h, ← hde, hg', mul_inv_cancel_right]
      _ = d := by rw [mul_assoc, ht2, mul_one]

open scoped IsMulCommutative in
theorem eq_bot_of_odd_normal_quot {C : Type*} [Group C] [Finite C] {z : C}
    (hz : ∀ g : C, g * z = z * g) (hz2 : z * z = 1)
    (hO : ∀ N : Subgroup C, N.Normal → Odd (Nat.card N) → N = ⊥)
    [(Subgroup.zpowers z).Normal] (M : Subgroup (C ⧸ Subgroup.zpowers z)) (hM : M.Normal)
    (hodd : Odd (Nat.card M)) : M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.zpowers z
  set N := M.comap (QuotientGroup.mk' Z)
  have hNn : N.Normal := Subgroup.Normal.comap hM _
  have hZN : Z ≤ N := fun x hx => by
    show (x : C ⧸ Z) ∈ M
    rw [(QuotientGroup.eq_one_iff x).2 hx]
    exact M.one_mem
  have hzN : z ∈ N := hZN (Subgroup.mem_zpowers z)
  set zN : N := ⟨z, hzN⟩
  set A := Subgroup.zpowers zN
  have hzN2 : zN * zN = 1 := Subtype.ext hz2
  have hAmem : ∀ x : N, x ∈ A ↔ x = 1 ∨ x = zN := by
    intro x
    rw [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
      · left
        rw [hj, zpow_mul, zpow_two, hzN2, one_zpow]
      · right
        rw [hj, zpow_add, zpow_mul, zpow_two, hzN2, one_zpow, one_mul, zpow_one]
    · rintro (rfl | rfl)
      · exact ⟨0, zpow_zero _⟩
      · exact ⟨1, zpow_one _⟩
  have hAcen : ∀ a ∈ A, ∀ n : N, n * a = a * n := by
    intro a ha n
    rcases (hAmem a).1 ha with rfl | rfl
    · rw [one_mul, mul_one]
    · exact Subtype.ext (hz n)
  let f : N →* M := ((QuotientGroup.mk' Z).comp N.subtype).codRestrict M fun x => x.2
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hfker : ∀ n : N, f n = 1 ↔ n ∈ A := by
    intro n
    have h1 : f n = 1 ↔ (n : C) ∈ Z := by
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff (n : C)
    rw [h1, hAmem]
    rw [show Z = Subgroup.zpowers z from rfl, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      have : n = zN ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
      rw [this]
      exact (hAmem _).1 (Subgroup.zpow_mem_zpowers zN k)
    · rintro (rfl | rfl)
      · exact ⟨0, zpow_zero _⟩
      · exact ⟨1, zpow_one _⟩
  have hidx : A.index = Nat.card M := by
    have h1 := Subgroup.card_ker_mul_card_range f
    have hker : f.ker = A := by
      ext n
      rw [MonoidHom.mem_ker, hfker]
    rw [hker, MonoidHom.range_eq_top.2 hfsurj, Subgroup.card_top] at h1
    have h2 := Subgroup.card_mul_index A
    have hpos : 0 < Nat.card A := Nat.card_pos
    rw [← h2] at h1
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  have hmodd : Odd A.index := hidx ▸ hodd
  let τ : N →* A := (MonoidHom.id A).transfer
  have hτ : ∀ n : N, ((τ n : A) : N) = n ^ A.index := by
    intro n
    have h := MonoidHom.transfer_eq_pow (MonoidHom.id A) n (fun k g₀ hk => by
      have hc := hAcen _ hk g₀
      have e : g₀ * (g₀⁻¹ * n ^ k * g₀) * g₀⁻¹ = g₀⁻¹ * n ^ k * g₀ := by
        rw [hc, mul_inv_cancel_right]
      rw [← e]
      group)
    rw [h]
    rfl
  have hpow_odd : ∀ y : N, y * y = 1 → y ^ A.index = y := by
    intro y hy
    obtain ⟨j, hj⟩ := hmodd
    rw [hj, pow_succ, pow_mul, sq, hy, one_pow, one_mul]
  have hmemK : ∀ n : N, n ∈ τ.ker ↔ n ^ A.index = 1 := by
    intro n
    rw [MonoidHom.mem_ker, ← hτ]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Subtype.ext h
  have hKn : (τ.ker.map N.subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨n, hn, rfl⟩ := hx
    have hgn : g * (n : C) * g⁻¹ ∈ N := hNn.conj_mem _ n.2 g
    refine ⟨⟨_, hgn⟩, (hmemK _).2 (Subtype.ext ?_), rfl⟩
    have h1 : ((n ^ A.index : N) : C) = 1 := by rw [(hmemK n).1 hn]; rfl
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
    rw [_root_.conj_pow, h1, mul_one, mul_inv_cancel]
  have hKodd : Odd (Nat.card (τ.ker.map N.subtype)) := by
    rw [Subgroup.card_map_of_injective N.subtype_injective, Nat.odd_iff]
    by_contra h2
    have h2' : 2 ∣ Nat.card τ.ker := by omega
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2'
    have hy2 : (y : N) * y = 1 := by
      rw [← sq, ← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
    have hy1 := (hmemK y).1 y.2
    rw [hpow_odd _ hy2] at hy1
    have : y = 1 := Subtype.ext hy1
    rw [this, orderOf_one] at hy
    exact absurd hy (by decide)
  have hKbot : τ.ker = ⊥ := by
    have h := hO _ hKn hKodd
    rw [Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at h
    exact h
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨n, hn⟩ := hfsurj ⟨y, hy⟩
  have hnA : n ∈ A := by
    have hτA := (τ n).2
    rw [hτ] at hτA
    rcases (hAmem _).1 hτA with h | h
    · have hn1 : n = 1 := by
        rw [← Subgroup.mem_bot, ← hKbot]
        exact (hmemK n).2 h
      rw [hn1]
      exact A.one_mem
    · have hcomm : n * zN = zN * n := hAcen zN (Subgroup.mem_zpowers zN) n
      have hK : n * zN ∈ τ.ker := by
        rw [hmemK, (show Commute n zN from hcomm).mul_pow, h, hpow_odd zN hzN2, hzN2]
      rw [hKbot, Subgroup.mem_bot] at hK
      have hn' : n = zN := by
        rw [← mul_inv_eq_one, show zN⁻¹ = zN from inv_eq_of_mul_eq_one_left hzN2]
        exact hK
      rw [hn']
      exact Subgroup.mem_zpowers zN
  have hf1 := (hfker n).2 hnA
  rw [hn] at hf1
  exact congrArg Subtype.val hf1

theorem centralizer_le_range_of_twoC
    {G : Type} [Group G] [Finite G] {d : G} (hd : d ≠ 1)
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) {u : CVert}
    (hu : u ∈ sphereDistThree cv0)
    (hO : CFSG.oddCore (Subgroup.centralizer {Φ ((cV0 : Shat) * clabelS u)}) = ⊥) :
    Subgroup.centralizer {Φ ((cV0 : Shat) * clabelS u)} ≤ Φ.range := by
  have hx : (cV0 : Shat) * clabelS u * ((cV0 : Shat) * clabelS u) = 1 := by
    rw [← sq, ← orderOf_cV0_mul_clabelS hu, pow_orderOf_eq_one]
  have ht2 : Φ ((cV0 : Shat) * clabelS u) * Φ ((cV0 : Shat) * clabelS u) = 1 := by
    rw [← map_mul, hx, map_one]
  refine centralizer_le_range_of_twoC_quot hd ψ Φ hΦ hDM hu fun N hN hNodd => ?_
  exact eq_bot_of_odd_normal_quot
    (fun g => Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)) (Subtype.ext ht2)
    (oddCore_eq_bot_iff.1 hO) N hN hNodd

theorem centralizer_le_range_of_rankS_eq_2158
    {G : Type} [Group G] [Finite G] {d : G}
    (hd : d ≠ 1) (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G)
    (hΦ : ∀ a : vStab cv0, Φ a = psiInvHom ψ a)
    (hDM : conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d) {s : Shat}
    (hs : orderOf s = 2) (hrk : rankS s = 2158)
    (hO : CFSG.oddCore (Subgroup.centralizer {Φ s}) = ⊥) :
    Subgroup.centralizer {Φ s} ≤ Φ.range := by
  obtain ⟨u, hu, hru⟩ := exists_rankS_clabelS_mul
  have hconj := isConj_of_rankS_eq (orderOf_cV0_mul_clabelS hu) hs (hru.trans hrk.symm)
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  have hg' : Φ g * Φ ((cV0 : Shat) * clabelS u) * (Φ g)⁻¹ = Φ s := by
    rw [← map_inv, ← map_mul, ← map_mul, hg]
  have h := centralizer_le_range_of_twoC hd ψ Φ hΦ hDM hu
    (oddCore_eq_bot_of_equiv (centralizerConjEquiv (Φ g) hg') hO)
  rw [← hg']
  exact centralizer_conj_le_range h ⟨g, rfl⟩

end CFSG.Monster.B.GSide

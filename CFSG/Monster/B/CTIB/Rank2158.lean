module

public import CFSG.Monster.B.CTIB.Rank2158Witness
public import CFSG.Monster.B.TwoA.Amalgam.NativeChain
public import CFSG.Monster.B.TwoA.Amalgam.DistTwoInst
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
public import CFSG.Monster.B.CTIB.Rep4371Main

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA.Sp8
open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

@[expose] def DistThreeProductInput :
    Prop :=
  ∀ v w : CVert, cgraph.dist v w = 3 →
    ∃ F : Subgroup (Subgroup.centralizer {clabelS v * clabelS w}), CFSG.IsComponent F ∧
      (∀ K : Subgroup (Subgroup.centralizer {clabelS v * clabelS w}), CFSG.IsComponent K →
        K = F) ∧
      IsSimpleGroup F ∧ Nonempty (F ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
      Nat.card F = 3311126603366400

@[expose] noncomputable def xhatS : Shat := ⟨xhat, Ehat_le_Shat xhat_mem_Ehat⟩

theorem sEquiv_xs : sEquiv xs = xhatS := by
  apply Subtype.ext
  show (iotaD xs.unop)⁻¹ = xhat
  rw [xs, unop_op, iotaD_xbar]
  exact inv_eq_of_mul_eq_one_left xhat_mul_self

theorem cS_inv : cS⁻¹ = cS := by
  apply Subtype.ext
  show cQ⁻¹ = cQ
  exact inv_eq_of_mul_eq_one_left cQ_mul_self

private theorem isConj_map_iff {G H : Type*} [Group G] [Group H] (f : G ≃* H) {a b : G} :
    IsConj (f a) (f b) ↔ IsConj a b := by
  constructor
  · intro h
    have h' := f.symm.toMonoidHom.map_isConj h
    simpa using h'
  · exact f.toMonoidHom.map_isConj

theorem isConj_clabelS_mul_of_adj
    {v a : CVert} (h : cgraph.Adj v a) :
    IsConj (clabelS v * clabelS a) xhatS := by
  obtain ⟨s, hs⟩ := cvMul_transitive cv0 v
  obtain ⟨e, he⟩ := exists_eq_cvMul_nbr hs h
  have hv : clabel v = (s : Dfull)⁻¹ * cQ * s := by rw [← hs, clabel_cvMul, clabel_cv0]
  have ha : clabel a = (s : Dfull)⁻¹ * (cQ * ((e : Dfull)⁻¹ * xhat * e)) * s := by
    rw [he, clabel_cvMul, clabel_nbr]
  refine isConj_iff.2 ⟨⟨(e : Dfull), Eam_le_Shat e.2⟩ * s, Subtype.ext ?_⟩
  show (e : Dfull) * s * (clabel v * clabel a) * ((e : Dfull) * s)⁻¹ = xhat
  rw [hv, ha]
  calc (e : Dfull) * s * ((s : Dfull)⁻¹ * cQ * s *
        ((s : Dfull)⁻¹ * (cQ * ((e : Dfull)⁻¹ * xhat * e)) * s)) * ((e : Dfull) * s)⁻¹ =
        (e : Dfull) * (cQ * cQ) * (e : Dfull)⁻¹ * xhat := by group
    _ = xhat := by rw [cQ_mul_self, mul_one, mul_inv_cancel, one_mul]

theorem orderOf_clabel_mul_dvd
    {v u : CVert} (hc : Commute (clabelS v) (clabelS u)) :
    orderOf (clabel v * clabel u) ∣ 2 := by
  apply orderOf_dvd_of_pow_eq_one
  have hc' : clabel v * clabel u = clabel u * clabel v := congrArg Subtype.val hc.eq
  have h1 : clabel v * clabel v = 1 := by rw [← sq, ← orderOf_clabel v, pow_orderOf_eq_one]
  have h2 : clabel u * clabel u = 1 := by rw [← sq, ← orderOf_clabel u, pow_orderOf_eq_one]
  calc (clabel v * clabel u) ^ 2 = clabel v * (clabel u * clabel v) * clabel u := by
        rw [sq]; group
    _ = clabel v * (clabel v * clabel u) * clabel u := by rw [hc']
    _ = (clabel v * clabel v) * (clabel u * clabel u) := by group
    _ = 1 := by rw [h1, h2, one_mul]

theorem dist_eq_three_of_commute
    (hamb : AmbientRootOrbitsHyp) {v u : CVert}
    (hne : clabelS v ≠ clabelS u) (hc : Commute (clabelS v) (clabelS u))
    (hx : ¬ IsConj (clabelS v * clabelS u) xhatS) : cgraph.dist v u = 3 := by
  have hle := (diameter_three_rank_five_of_ambient hamb).1 v u
  have hvu : v ≠ u := fun e => hne (by rw [e])
  have h0 : cgraph.dist v u ≠ 0 := fun h =>
    hvu ((cgraph_connected.preconnected v u).dist_eq_zero_iff.1 h)
  have h1 : cgraph.dist v u ≠ 1 := fun h =>
    hx (isConj_clabelS_mul_of_adj (SimpleGraph.dist_eq_one_iff_adj.1 h))
  have h2 : cgraph.dist v u ≠ 2 := by
    intro h
    have hle2 : lblOrd v u ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_clabel_mul_dvd hc)
    rcases labelThree_or_labelFour_of_dist exists_rootModel h with h3 | h4
    · rcases h3.1 with e | e <;> omega
    · rcases h4.1 with e | e <;> omega
  omega

theorem exists_clabelS_eq
    (hamb : AmbientRootOrbitsHyp) {t : Sbp} (ht : IsConj t labelS) :
    ∃ v : CVert, clabelS v = sEquiv t := by
  have h1 : IsConj (sEquiv t) cS := by
    have h := (isConj_map_iff sEquiv).2 ht
    rwa [sEquiv_labelS, cS_inv] at h
  obtain ⟨g, hg⟩ := isConj_iff.1 h1
  have hg' : sEquiv t = g⁻¹ * cS * g := by rw [← hg]; group
  have hmem : ((sEquiv t : Shat) : Dfull) ∈ Set.range clabel := by
    rw [(global_label_of_ambient hamb).2.1]
    exact ⟨g, congrArg Subtype.val hg'⟩
  obtain ⟨v, hv⟩ := hmem
  exact ⟨v, Subtype.ext hv⟩

theorem exists_witness_pair
    (hamb : AmbientRootOrbitsHyp) :
    ∃ v u : CVert, cgraph.dist v u = 3 ∧ clabelS v * clabelS u = sEquiv (rs 6 * e2158) := by
  obtain ⟨v, hv⟩ := exists_clabelS_eq hamb isConj_rs6_labelS
  obtain ⟨u, hu⟩ := exists_clabelS_eq hamb isConj_e2158_labelS
  refine ⟨v, u, dist_eq_three_of_commute hamb ?_ ?_ ?_, by rw [hv, hu, map_mul]⟩
  · rw [hv, hu]
    exact fun e => rs6_ne_e2158 (sEquiv.injective e)
  · rw [hv, hu]
    exact commute_rs6_e2158.map sEquiv
  · rw [hv, hu, ← map_mul, ← sEquiv_xs, isConj_map_iff]
    intro h
    have e1 := rank_beta_conj h
    have e2 := rank_beta_conj isConj_rs6_mul_e2158
    rw [← rs0_eq] at e1
    obtain ⟨-, h0, h5, -⟩ := rank_four
    omega

theorem centralizer_equiv_of_isConj {G : Type*} [Group G] {s t : G} (h : IsConj s t) :
    Nonempty (Subgroup.centralizer {s} ≃* Subgroup.centralizer {t}) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have e1 : (MulAut.conj c) s = t := by rw [MulAut.conj_apply, hc]
  exact ⟨(centralizerEquiv (MulAut.conj c) s).trans (MulEquiv.subgroupCongr (by rw [e1]))⟩

theorem unique_component_of_mulEquiv {G H : Type*} [Group G] [Group H] (Ψ : G ≃* H)
    {F : Subgroup H} (hF : CFSG.IsComponent F)
    (hU : ∀ K : Subgroup H, CFSG.IsComponent K → K = F) :
    CFSG.IsComponent (F.map Ψ.symm.toMonoidHom) ∧
      (∀ K : Subgroup G, CFSG.IsComponent K → K = F.map Ψ.symm.toMonoidHom) ∧
      Nonempty (F.map Ψ.symm.toMonoidHom ≃* F) := by
  refine ⟨CFSG.LocalCores.isComponent_map_mulEquiv Ψ.symm hF, fun K hK => ?_,
    ⟨(F.equivMapOfInjective Ψ.symm.toMonoidHom Ψ.symm.injective).symm⟩⟩
  have h := hU _ (CFSG.LocalCores.isComponent_map_mulEquiv Ψ hK)
  rw [← h, CFSG.LocalCores.map_map_symm]

theorem f4_component_of_mulEquiv {G H : Type*} [Group G] [Group H] (Ψ : G ≃* H)
    (hH : ∃ F : Subgroup H, CFSG.IsComponent F ∧
      (∀ K : Subgroup H, CFSG.IsComponent K → K = F) ∧
      IsSimpleGroup F ∧ Nonempty (F ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
      Nat.card F = 3311126603366400) :
    ∃ K : Subgroup G, CFSG.IsComponent K ∧ (∀ K' : Subgroup G, CFSG.IsComponent K' → K' = K) ∧
      IsSimpleGroup K ∧ Nonempty (K ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
      Nat.card K = 3311126603366400 ∧ 17 ∣ Nat.card K := by
  obtain ⟨F, hF, hU, hS, ⟨eF⟩, hcard⟩ := hH
  obtain ⟨hK, hKU, ⟨eK⟩⟩ := unique_component_of_mulEquiv Ψ hF hU
  have hcK : Nat.card (F.map Ψ.symm.toMonoidHom) = 3311126603366400 :=
    (Nat.card_congr eK.toEquiv).trans hcard
  exact ⟨_, hK, hKU, @MulEquiv.isSimpleGroup _ _ _ _ hS eK, ⟨eK.trans eF⟩, hcK,
    by rw [hcK]; norm_num⟩

theorem isConj_rs5_of_rank
    {s : Sbp} (hs : orderOf s = 2) (hr : ((βr s) - 1).rank = 2158) :
    IsConj s (rs 5) := by
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := four_classes co2_involution_input hs
  have e := rank_beta_conj hc
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  have hi5 : i = 5 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> omega
  subst hi5
  exact hc

theorem native_rank_2158_distance_three_product_of
    (hamb : AmbientRootOrbitsHyp)
    (hD : DistThreeProductInput) :
    (∃ v u : CVert, cgraph.dist v u = 3 ∧ IsConj (sEquiv (rs 5)) (clabelS v * clabelS u)) ∧
    (∀ s : Sbp, orderOf s = 2 → ((βr s) - 1).rank = 2158 →
      ∃ K : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K ∧
        (∀ K' : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K' → K' = K) ∧
        IsSimpleGroup K ∧ Nonempty (K ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
        Nat.card K = 3311126603366400 ∧ 17 ∣ Nat.card K) ∧
    ∀ X : NativeSporadic.B, orderOf X = 2 → (X.val.val - 1).rank = 2158 →
      ∃ K : Subgroup (Subgroup.centralizer {X}), CFSG.IsComponent K ∧
        (∀ K' : Subgroup (Subgroup.centralizer {X}), CFSG.IsComponent K' → K' = K) ∧
        IsSimpleGroup K ∧ Nonempty (K ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
        Nat.card K = 3311126603366400 ∧ 17 ∣ Nat.card K := by
  obtain ⟨v, u, hvu, hd⟩ := exists_witness_pair hamb
  have hS : ∀ s : Sbp, orderOf s = 2 → ((βr s) - 1).rank = 2158 →
      ∃ K : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K ∧
        (∀ K' : Subgroup (Subgroup.centralizer {s}), CFSG.IsComponent K' → K' = K) ∧
        IsSimpleGroup K ∧ Nonempty (K ≃* adjointGroup Tag.F4 (ZMod 2)) ∧
        Nat.card K = 3311126603366400 ∧ 17 ∣ Nat.card K := by
    intro s hs hr
    obtain ⟨Ψ₁⟩ := centralizer_equiv_of_isConj
      ((isConj_rs5_of_rank hs hr).trans isConj_rs6_mul_e2158.symm)
    have Ψ₂ : Subgroup.centralizer {rs 6 * e2158} ≃*
        Subgroup.centralizer {clabelS v * clabelS u} :=
      (centralizerEquiv sEquiv (rs 6 * e2158)).trans (MulEquiv.subgroupCongr (by rw [hd]))
    exact f4_component_of_mulEquiv (Ψ₁.trans Ψ₂) (hD v u hvu)
  refine ⟨⟨v, u, hvu, ?_⟩, hS, fun X hX hr => ?_⟩
  · rw [hd]
    exact (isConj_map_iff sEquiv).2 isConj_rs6_mul_e2158.symm
  · have hX' : orderOf (iotaEquiv X) = 2 := by rw [MulEquiv.orderOf_eq]; exact hX
    have hr' : ((βr (iotaEquiv X)) - 1).rank = 2158 := by
      rw [← rank_iotaEquiv_symm, MulEquiv.symm_apply_apply]
      exact hr
    obtain ⟨K, hK, hKU, hKS, hKe, hKc, -⟩ := hS (iotaEquiv X) hX' hr'
    have Ψ : Subgroup.centralizer {X} ≃* Subgroup.centralizer {iotaEquiv X} := by
      with_reducible_and_instances exact centralizerEquiv iotaEquiv X
    exact f4_component_of_mulEquiv Ψ ⟨K, hK, hKU, hKS, hKe, hKc⟩

end CFSG.Monster.B.CTIB

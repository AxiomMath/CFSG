module

public import CFSG.Monster.B.CTIB.HOuterCert
public import CFSG.Monster.B.CTIB.HInner
public import CFSG.Monster.B.CTIB.Rank2158
public import CFSG.Monster.B.CTIB.DistThreeProductCore
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
public import Certificates.Certificate3122
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

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
open CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

section Generic

variable {A B : Type*} [Group A] [Group B]

theorem eq_one_or_eq_of_mem_zpowers {c y : A} (hc : orderOf c = 2)
    (hy : y ∈ Subgroup.zpowers c) : y = 1 ∨ y = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_mod_orderOf, hc]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]

theorem fiber_eq_pair (ρ : A →* B) {c : A} (hker : ρ.ker = Subgroup.zpowers c)
    (hc : orderOf c = 2) (y : A) : {a : A | ρ a = ρ y} = {y, c * y} := by
  have hc1 : ρ c = 1 := MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_zpowers c)
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have hk : a * y⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
    rw [hker] at hk
    rcases eq_one_or_eq_of_mem_zpowers hc hk with h1 | h1
    · exact Or.inl (mul_inv_eq_one.1 h1)
    · exact Or.inr (by rw [← h1, inv_mul_cancel_right])
  · rintro (rfl | rfl)
    · rfl
    · rw [map_mul, hc1, one_mul]

theorem isConj_map_iff_of_ker (ρ : A →* B) (hsurj : Function.Surjective ρ) {c : A}
    (hker : ρ.ker = Subgroup.zpowers c) (hc : orderOf c = 2) (a y : A) :
    IsConj (ρ a) (ρ y) ↔ IsConj a y ∨ IsConj a (c * y) := by
  have hc1 : ρ c = 1 := MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_zpowers c)
  constructor
  · intro h
    obtain ⟨γ, hγ⟩ := isConj_iff.1 h
    obtain ⟨g, rfl⟩ := hsurj γ
    have hmem : g * a * g⁻¹ ∈ {x : A | ρ x = ρ y} := by
      show ρ (g * a * g⁻¹) = ρ y
      rw [map_mul, map_mul, map_inv, hγ]
    rw [fiber_eq_pair ρ hker hc y] at hmem
    rcases hmem with h1 | h1
    · exact Or.inl (isConj_iff.2 ⟨g, h1⟩)
    · exact Or.inr (isConj_iff.2 ⟨g, h1⟩)
  · rintro (h | h)
    · exact ρ.map_isConj h
    · have h' := ρ.map_isConj h
      rwa [map_mul, hc1, one_mul] at h'

@[expose] def centralizerRestrict (ρ : A →* B) (y : A) :
    Subgroup.centralizer {y} →* Subgroup.centralizer {ρ y} :=
  (ρ.comp (Subgroup.centralizer {y}).subtype).codRestrict _ fun a => by
    have ha : Commute (a : A) y := Subgroup.mem_centralizer_singleton_iff.1 a.2
    exact Subgroup.mem_centralizer_singleton_iff.2 (ha.map ρ)

theorem natCard_centralizer_eq_two_mul [Finite A] (ρ : A →* B) (hsurj : Function.Surjective ρ)
    {c : A} (hcen : c ∈ Subgroup.center A) (hker : ρ.ker = Subgroup.zpowers c)
    (hc : orderOf c = 2) {y : A} (hy : ¬ IsConj y (c * y)) :
    Nat.card (Subgroup.centralizer {y}) = 2 * Nat.card (Subgroup.centralizer {ρ y}) := by
  have hc1 : ρ c = 1 := MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_zpowers c)
  have hsurj' : Function.Surjective (centralizerRestrict ρ y) := by
    rintro ⟨γ, hγ⟩
    obtain ⟨g, rfl⟩ := hsurj γ
    have hγ' : Commute (ρ g) (ρ y) := Subgroup.mem_centralizer_singleton_iff.1 hγ
    have hmem : g * y * g⁻¹ ∈ {x : A | ρ x = ρ y} := by
      show ρ (g * y * g⁻¹) = ρ y
      rw [map_mul, map_mul, map_inv, hγ'.eq, mul_inv_cancel_right]
    rw [fiber_eq_pair ρ hker hc y] at hmem
    rcases hmem with h1 | h1
    · have hg : g ∈ Subgroup.centralizer {y} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1
      exact ⟨⟨g, hg⟩, rfl⟩
    · exact absurd (isConj_iff.2 ⟨g, h1⟩) hy
  have hk : Nat.card (centralizerRestrict ρ y).ker = 2 := by
    have hcz : ∀ w : A, w ∈ Subgroup.zpowers c → w ∈ Subgroup.centralizer {y} := fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_center_iff.1 ((Subgroup.zpowers_le.2 hcen) hw) y).symm
    rw [← hc, ← Nat.card_zpowers]
    refine Nat.card_congr
      { toFun := fun a => ⟨((a : Subgroup.centralizer {y}) : A), ?_⟩
        invFun := fun w => ⟨⟨w, hcz w w.2⟩, ?_⟩
        left_inv := fun a => rfl
        right_inv := fun w => rfl }
    · rw [← hker, MonoidHom.mem_ker]
      exact congrArg Subtype.val (MonoidHom.mem_ker.1 a.2)
    · rw [MonoidHom.mem_ker]
      refine Subtype.ext ?_
      show ρ w = 1
      rw [← MonoidHom.mem_ker, hker]
      exact w.2
  have h := Subgroup.card_ker_mul_card_of_surjective hsurj'
  rw [hk] at h
  exact h.symm

theorem exists_conj_map_eq (ρ : A →* B) (hsurj : Function.Surjective ρ) {s : A} {β : B}
    (h : IsConj (ρ s) β) : ∃ k : A, ρ (k * s * k⁻¹) = β := by
  obtain ⟨γ, hγ⟩ := isConj_iff.1 h
  obtain ⟨k, rfl⟩ := hsurj γ
  exact ⟨k, by rw [map_mul, map_mul, map_inv, hγ]⟩

theorem map_mul_of_ker (ρ : A →* B) {c : A} (hker : ρ.ker = Subgroup.zpowers c) (y : A) :
    ρ (c * y) = ρ y := by
  rw [map_mul, MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_zpowers c), one_mul]

theorem conj_eq_or_of_commute_map (ρ : A →* B) {c : A} (hker : ρ.ker = Subgroup.zpowers c)
    (hc : orderOf c = 2) {a y : A} (h : Commute (ρ a) (ρ y)) :
    a * y * a⁻¹ = y ∨ a * y * a⁻¹ = c * y := by
  have hmem : a * y * a⁻¹ ∈ {x : A | ρ x = ρ y} := by
    show ρ (a * y * a⁻¹) = ρ y
    rw [map_mul, map_mul, map_inv, h.eq, mul_inv_cancel_right]
  rw [fiber_eq_pair ρ hker hc y] at hmem
  exact hmem

theorem commute_of_conj_eq {a y : A} (h : a * y * a⁻¹ = y) : Commute a y := by
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h

theorem mul_mul_cancel_of_mul_self {c y : A} (hc : c * c = 1) : c * (c * y) = y := by
  rw [← mul_assoc, hc, one_mul]

theorem orderOf_eq_two_of {y : A} (hy : y * y = 1) (hne : y ≠ 1) : orderOf y = 2 :=
  orderOf_eq_prime (by rw [sq]; exact hy) hne

theorem mul_self_mul_of_commute {a b : A} (h : Commute a b) (ha : a * a = 1) (hb : b * b = 1) :
    a * b * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by rw [mul_assoc, mul_assoc, mul_assoc]
    _ = a * (a * b) * b := by rw [h.eq]
    _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]

theorem not_isConj_of_map (ρ : A →* B) {a y : A} (h : ¬ IsConj (ρ a) (ρ y)) : ¬ IsConj a y :=
  fun h' => h (ρ.map_isConj h')

theorem outer_fibres_of [Finite A] (ρ : A →* B) (hsurj : Function.Surjective ρ) {c : A}
    (hcen : c ∈ Subgroup.center A) (hker : ρ.ker = Subgroup.zpowers c) (hc : orderOf c = 2)
    {b x : A} {β₀ τ₀ : B} (hbx : Commute b x) (hb : ρ b = β₀) (hx : ρ (b * x) = τ₀)
    (hbb : b * b = 1) (hxx : x * x = 1) (hβ₀ : β₀ ≠ 1) (hτ₀ : τ₀ ≠ 1)
    (hn1 : ¬ IsConj b (c * b)) (hn2 : ¬ IsConj (b * x) (c * (b * x)))
    (hn3 : ¬ IsConj β₀ τ₀) :
    {y : A | ρ y = β₀} = {b, c * b} ∧ {y : A | ρ y = τ₀} = {b * x, c * (b * x)} ∧
    (∀ y : A, IsConj (ρ y) β₀ ↔ IsConj y b ∨ IsConj y (c * b)) ∧
    (∀ y : A, IsConj (ρ y) τ₀ ↔ IsConj y (b * x) ∨ IsConj y (c * (b * x))) ∧
    orderOf b = 2 ∧ orderOf (c * b) = 2 ∧ orderOf (b * x) = 2 ∧ orderOf (c * (b * x)) = 2 ∧
    Nat.card (Subgroup.centralizer {b}) = 2 * Nat.card (Subgroup.centralizer {β₀}) ∧
    Nat.card (Subgroup.centralizer {c * b}) = 2 * Nat.card (Subgroup.centralizer {β₀}) ∧
    Nat.card (Subgroup.centralizer {b * x}) = 2 * Nat.card (Subgroup.centralizer {τ₀}) ∧
    Nat.card (Subgroup.centralizer {c * (b * x)}) = 2 * Nat.card (Subgroup.centralizer {τ₀}) ∧
    ¬ IsConj (c * b) (c * (b * x)) := by
  have hcc : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have hcb : ρ (c * b) = β₀ := (map_mul_of_ker ρ hker b).trans hb
  have hcbx : ρ (c * (b * x)) = τ₀ := (map_mul_of_ker ρ hker _).trans hx
  have hcomm : ∀ y : A, Commute c y := fun y => (Subgroup.mem_center_iff.1 hcen y).symm
  have hne : ∀ y : A, ρ y ≠ 1 → y ≠ 1 := fun y h e => h (by rw [e, map_one])
  have hbxbx : b * x * (b * x) = 1 := mul_self_mul_of_commute hbx hbb hxx
  refine ⟨by rw [← hb]; exact fiber_eq_pair ρ hker hc b,
    by rw [← hx]; exact fiber_eq_pair ρ hker hc _,
    fun y => by rw [← hb]; exact isConj_map_iff_of_ker ρ hsurj hker hc y b,
    fun y => by rw [← hx]; exact isConj_map_iff_of_ker ρ hsurj hker hc y _,
    orderOf_eq_two_of hbb (hne b (by rw [hb]; exact hβ₀)),
    orderOf_eq_two_of (mul_self_mul_of_commute (hcomm b) hcc hbb) (hne _ (by rw [hcb]; exact hβ₀)),
    orderOf_eq_two_of hbxbx (hne _ (by rw [hx]; exact hτ₀)),
    orderOf_eq_two_of (mul_self_mul_of_commute (hcomm _) hcc hbxbx)
      (hne _ (by rw [hcbx]; exact hτ₀)), ?_, ?_, ?_, ?_,
    not_isConj_of_map ρ (by rw [hcb, hcbx]; exact hn3)⟩
  · rw [← hb]
    exact natCard_centralizer_eq_two_mul ρ hsurj hcen hker hc hn1
  · rw [← hcb]
    refine natCard_centralizer_eq_two_mul ρ hsurj hcen hker hc ?_
    rw [mul_mul_cancel_of_mul_self hcc]
    exact fun h => hn1 h.symm
  · rw [← hx]
    exact natCard_centralizer_eq_two_mul ρ hsurj hcen hker hc hn2
  · rw [← hcbx]
    refine natCard_centralizer_eq_two_mul ρ hsurj hcen hker hc ?_
    rw [mul_mul_cancel_of_mul_self hcc]
    exact fun h => hn2 h.symm

end Generic

theorem rank_conj_shat
    {a b : Shat} (h : IsConj a b) :
    ((βr (sEquiv.symm a)) - 1).rank = ((βr (sEquiv.symm b)) - 1).rank :=
  rank_beta_conj (sEquiv.symm.toMonoidHom.map_isConj h)

theorem sEquiv_symm_cS :
    sEquiv.symm cS = labelS := by
  rw [MulEquiv.symm_apply_eq, sEquiv_labelS, cS_inv]

theorem rank_labelS :
    ((βr labelS) - 1).rank = 1860 :=
  (rank_beta_conj isConj_rs6_labelS).symm.trans ((rank_rs (i := 6) (by norm_num)).trans rfl)

theorem rank_clabelS
    (p : CVert) : ((βr (sEquiv.symm (clabelS p))) - 1).rank = 1860 := by
  rw [rank_conj_shat (isConj_clabelS p cv0), clabelS_cv0, sEquiv_symm_cS, rank_labelS]

theorem rank_xhatS :
    ((βr (sEquiv.symm xhatS)) - 1).rank = 2048 := by
  rw [← sEquiv_xs, MulEquiv.symm_apply_apply, ← rs0_eq]
  exact rank_four.2.1

theorem exists_pair_cvMul
    {p q v u : CVert} (hpq : cgraph.dist p q = 3)
    (hvu : cgraph.dist v u = 3) : ∃ g : Shat, cvMul p g = v ∧ cvMul q g = u := by
  obtain ⟨g₁, hg₁⟩ := cvMul_transitive p v
  have hq₁ : cvMul q g₁ ∈ sphereDistThree v := by
    rw [← hg₁]
    exact sphereDistThree_cvMul (mem_sphereDistThree.2 hpq) g₁
  obtain ⟨g₂, hv, hu⟩ := (distThreePaths_of_ambient ambientRootOrbitsHyp).1 v _ u hq₁
    (mem_sphereDistThree.2 hvu)
  exact ⟨g₁ * g₂, by rw [cvMul_mul, hg₁, hv], by rw [cvMul_mul, hu]⟩

theorem rank_clabelS_mul_of_dist_three
    {p q : CVert} (hpq : cgraph.dist p q = 3) :
    ((βr (sEquiv.symm (clabelS p * clabelS q))) - 1).rank = 2158 := by
  obtain ⟨v, u, hvu, hd⟩ := exists_witness_pair ambientRootOrbitsHyp
  obtain ⟨g, hgp, hgq⟩ := exists_pair_cvMul hpq hvu
  have hconj : IsConj (clabelS p * clabelS q) (clabelS v * clabelS u) := by
    refine isConj_iff.2 ⟨g⁻¹, ?_⟩
    rw [← hgp, ← hgq, clabelS_cvMul, clabelS_cvMul]
    group
  rw [rank_conj_shat hconj, hd, MulEquiv.symm_apply_apply, rank_beta_conj isConj_rs6_mul_e2158]
  exact rank_four.2.2.1

theorem commute_xs_of_mem_Jbar
    {g : Sbp} (hg : g.unop ∈ Jbar) : Commute g xs := by
  have h := conj_xs hg
  calc g * xs = g * (g⁻¹ * xs * g) := by rw [h]
    _ = xs * g := by group

theorem commute_rs6_xs :
    Commute (rs 6) xs := by
  rw [rs6_eq, cosetElt]
  exact (commute_xs_of_mem_Jbar (hs_mem_Jbar (Or.inl rfl))).mul_left
    (xs_comm (qS_mem 10541)).symm

theorem e2158_mem_Qs :
    e2158 ∈ Qs := by
  rw [e2158_eq]
  exact qS_mem _

theorem commute_e2158_xs :
    Commute e2158 xs := (xs_comm e2158_mem_Qs).symm

theorem e2158_mul_self :
    e2158 * e2158 = 1 := by
  have h := isConj_e2158_labelS
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  have hl : labelS * labelS = 1 := by
    apply sEquiv.injective
    rw [map_mul, map_one, sEquiv_labelS, cS_inv]
    exact Subtype.ext Sp8.cQ_mul_self
  calc e2158 * e2158 = g⁻¹ * (labelS * labelS) * g := by rw [← hg]; group
    _ = 1 := by rw [hl]; group

theorem isConj_e2158_mul_xs_labelS :
    IsConj (e2158 * xs) labelS := by
  have hW := (conj_wordS' w2158_letters).2.2
  have h1 : IsConj (e2158 * xs) (qS 1 * xs) := by
    refine isConj_iff.2 ⟨wordS' w2158, ?_⟩
    have hx := conj_xs hW
    calc wordS' w2158 * (e2158 * xs) * (wordS' w2158)⁻¹ =
          wordS' w2158 * (e2158 * ((wordS' w2158)⁻¹ * xs * wordS' w2158)) *
            (wordS' w2158)⁻¹ := by rw [hx]
      _ = qS 1 * xs := by rw [e2158]; group
  have h2 : qS 1 * xs ∈ jClass (qS 1) := by
    refine mem_jClass_of (by decide) (Qs.mul_mem (qS_mem 1) xs_mem) ?_
    rw [psiS_mul (qS_mem 1) xs_mem, psiS_xs, add_zero]
    exact mem_jOrbit_self _
  exact h1.trans ((isConj_of_mem_jClass h2).trans (isConj_of_mem_jClass labelS_mem_jClass).symm)

theorem sEquiv_e2158_mul_e2158_xs :
    sEquiv e2158 * sEquiv (e2158 * xs) = sEquiv xs := by
  rw [← map_mul, ← mul_assoc, e2158_mul_self, one_mul]

theorem exists_frame :
    ∃ v₁ u₁ z₁ : CVert, clabelS v₁ = sEquiv e2158 ∧ clabelS u₁ = sEquiv (rs 6) ∧
      clabelS z₁ = sEquiv (e2158 * xs) ∧ cgraph.dist v₁ u₁ = 3 ∧ cgraph.Adj v₁ z₁ ∧
      Commute (clabelS u₁) (clabelS z₁) := by
  obtain ⟨v₁, hv₁⟩ := exists_clabelS_eq ambientRootOrbitsHyp isConj_e2158_labelS
  obtain ⟨u₁, hu₁⟩ := exists_clabelS_eq ambientRootOrbitsHyp isConj_rs6_labelS
  obtain ⟨z₁, hz₁⟩ := exists_clabelS_eq ambientRootOrbitsHyp isConj_e2158_mul_xs_labelS
  have hdiam := (diameter_three_rank_five_of_ambient ambientRootOrbitsHyp).1
  have hvu : cgraph.dist v₁ u₁ = 3 := by
    refine dist_eq_three_of_commute ambientRootOrbitsHyp ?_ ?_ ?_
    · rw [hv₁, hu₁]
      exact fun e => rs6_ne_e2158 (sEquiv.injective e).symm
    · rw [hv₁, hu₁]
      exact commute_rs6_e2158.symm.map sEquiv
    · rw [hv₁, hu₁, ← map_mul]
      intro h
      have e1 := rank_conj_shat h
      rw [MulEquiv.symm_apply_apply, rank_xhatS, commute_rs6_e2158.symm.eq,
        rank_beta_conj isConj_rs6_mul_e2158, rank_four.2.2.1] at e1
      omega
  have hvz : cgraph.Adj v₁ z₁ := by
    have hne : v₁ ≠ z₁ := by
      intro e
      have h := congrArg clabelS e
      rw [hv₁, hz₁] at h
      have h' := sEquiv.injective h
      exact xs_ne_one (by simpa using h'.symm)
    have hc : Commute (clabelS v₁) (clabelS z₁) := by
      rw [hv₁, hz₁]
      exact ((Commute.refl e2158).mul_right commute_e2158_xs).map sEquiv
    rcases adj_or_dist_three_of_commute hdiam hne hc with h | h
    · exact h
    · exfalso
      have e1 := rank_clabelS_mul_of_dist_three h
      have e2 : clabelS v₁ * clabelS z₁ = xhatS := by
        rw [hv₁, hz₁, ← map_mul, ← mul_assoc, e2158_mul_self, one_mul, sEquiv_xs]
      rw [e2, rank_xhatS] at e1
      omega
  refine ⟨v₁, u₁, z₁, hv₁, hu₁, hz₁, hvu, hvz, ?_⟩
  rw [hu₁, hz₁]
  exact (commute_rs6_e2158.mul_right commute_rs6_xs).map sEquiv

theorem cvMul_clabelS_eq_of_commute
    {u z : CVert} (h : Commute (clabelS u) (clabelS z)) :
    cvMul z (clabelS u) = z :=
  mem_vStab.1 ((commute_clabelS_iff (global_label_of_ambient ambientRootOrbitsHyp).1 z
    (clabelS u)).1 h)

theorem exists_triple_cvMul
    {v u z v₁ u₁ z₁ : CVert} (hvu : cgraph.dist v u = 3)
    (hvz : cgraph.Adj v z) (hz : Commute (clabelS u) (clabelS z)) (hvu₁ : cgraph.dist v₁ u₁ = 3)
    (hvz₁ : cgraph.Adj v₁ z₁) (hz₁ : Commute (clabelS u₁) (clabelS z₁)) :
    ∃ g : Shat, cvMul v g = v₁ ∧ cvMul u g = u₁ ∧ cvMul z g = z₁ := by
  obtain ⟨g₁, hg₁, hg₁'⟩ := exists_pair_cvMul hvu hvu₁
  have huv₁ : cgraph.dist u₁ v₁ = 3 := by rw [SimpleGraph.dist_comm]; exact hvu₁
  have hT := native_distance_three_pair_two_local_root_orbits_final huv₁
  have hset := hT.2.2.2.2.2.2.2.2.2.2.1
  have hz₂ : cvMul z g₁ ∈ cgraph.neighborSet v₁ \ sphereFour u₁ := by
    rw [← hset]
    refine ⟨?_, ?_⟩
    · show cgraph.Adj v₁ (cvMul z g₁)
      rw [← hg₁]
      exact (cgraph_adj_cvMul v z g₁).2 hvz
    · rw [← hg₁', clabelS_cvMul, ← cvMul_mul]
      have e : g₁ * (g₁⁻¹ * clabelS u * g₁) = clabelS u * g₁ := by group
      rw [e, cvMul_mul, cvMul_clabelS_eq_of_commute hz]
  have hz₁' : z₁ ∈ cgraph.neighborSet v₁ \ sphereFour u₁ := by
    rw [← hset]
    exact ⟨hvz₁, cvMul_clabelS_eq_of_commute hz₁⟩
  obtain ⟨s, hsu, hsv, hsz⟩ := hT.2.2.2.2.2.2.1 _ hz₂ _ hz₁'
  exact ⟨g₁ * s, by rw [cvMul_mul, hg₁, hsv], by rw [cvMul_mul, hg₁', hsu],
    by rw [cvMul_mul, hsz]⟩

section Local

variable {v : CVert} {ρ : vStab v →* GStar} {iv : cgraph.neighborSet v ≃ rootClass}

theorem exists_dist_three_beta
    (hρ : IsCompatLocal v ρ iv) :
    ∃ (u : CVert) (b : vStab v), cgraph.dist v u = 3 ∧ (b : Shat) = clabelS u ∧
      ρ b = betaStarElt := by
  obtain ⟨u₀, hu₀⟩ := sphereDistThree_nonempty_of_ambient ambientRootOrbitsHyp v
  have hvu₀ : cgraph.dist v u₀ = 3 := mem_sphereDistThree.1 hu₀
  obtain ⟨s₀, hs₀⟩ : ∃ s : vStab v, (s : Shat) = clabelS u₀ :=
    ⟨⟨clabelS u₀, (labelsInput_of_ambient ambientRootOrbitsHyp v u₀ hvu₀).1⟩, rfl⟩
  have hform := eq_inl_mul_beta
    (outerInput_of_ambient ambientRootOrbitsHyp v u₀ hvu₀ ρ iv hρ s₀ hs₀)
  have hs2 : s₀ * s₀ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hs₀, Subgroup.coe_one]
    exact clabelS_mul_clabelS u₀
  have hsq : (SemidirectProduct.inl (ρ s₀).left * betaStarElt) ^ 2 = 1 := by
    rw [← hform, sq, ← map_mul, hs2, map_one]
  rcases CFSG.Monster.B.E6.FieldInvF4.exists_conj_of_sq_eq_one hsq with ⟨g, hg⟩ | ⟨g, hg⟩
  · have hc : IsConj (ρ s₀) betaStarElt := by
      rw [hform]
      exact isConj_iff.2 ⟨SemidirectProduct.inl g, hg⟩
    obtain ⟨k, hk⟩ := exists_conj_map_eq ρ hρ.1 hc
    refine ⟨cvMul u₀ (k : Shat)⁻¹, k * s₀ * k⁻¹, ?_, ?_, hk⟩
    · have e := dist_cvMul v u₀ (k : Shat)⁻¹
      rwa [mem_vStab.1 ((vStab v).inv_mem k.2), hvu₀] at e
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hs₀, clabelS_cvMul, inv_inv]
  · exfalso
    have : Finite (vStab v) := Finite.of_injective _ Subtype.val_injective
    have hk := ker_eq_zpowers_cStab hρ.2.1
    have hcs := natCard_centralizer_le hk s₀
    have hρs : ρ s₀ = (SemidirectProduct.inl g)⁻¹ * CFSG.Monster.B.E6.FieldInvF4.tStar *
        (SemidirectProduct.inl g)⁻¹⁻¹ := by
      rw [hform]
      exact eq_conj_of_conj_eq hg
    have h2 : Nat.card (Subgroup.centralizer {ρ s₀}) = 95126814720 := by
      rw [hρs]
      exact (CFSG.Monster.B.E6.FieldInvF4.card_centralizer_conj _ _).trans
        CFSG.Monster.B.E6.FieldInvF4.card_centralizer_tStar
    obtain ⟨s, c, hsc⟩ := native_distance_three_canonical_F4_centralizer_image_final hvu₀
    have e : s = s₀ := Subtype.ext (hsc.1.trans hs₀.symm)
    have hcard : Nat.card (Subgroup.centralizer {s₀}) = 13244506413465600 :=
      e ▸ hsc.2.2.2.2.2.1
    omega

end Local

theorem coe_isConj
    {v : CVert} {a y : vStab v} (h : IsConj a y) : IsConj (a : Shat) (y : Shat) :=
  (vStab v).subtype.map_isConj h

theorem rootStar_mem_jStar :
    rootStar ∈ jStar := ⟨rootInv, rootInv_mem_groupJ, rfl⟩

theorem commute_betaStarElt_rootStar :
    Commute betaStarElt rootStar :=
  (commute_betaStarElt_of_mem_jStar rootStar_mem_jStar).symm

theorem not_isConj_betaStarElt_tStar :
    ¬ IsConj betaStarElt (rootStar * betaStarElt) := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  exact CFSG.Monster.B.E6.FieldInvF4.not_conj_betaStarElt_tStar g hg

section Config

variable {v : CVert} {ρ : vStab v →* GStar} {iv : cgraph.neighborSet v ≃ rootClass}

theorem exists_outer_config
    (hρ : IsCompatLocal v ρ iv) :
    ∃ (u z : CVert) (b w : vStab v), cgraph.dist v u = 3 ∧ cgraph.Adj v z ∧
      cgraph.dist u z = 3 ∧ (b : Shat) = clabelS u ∧ (w : Shat) = clabelS z ∧
      ρ b = betaStarElt ∧ ρ w = rootStar ∧ Commute b w := by
  have hinj := (global_label_of_ambient ambientRootOrbitsHyp).1
  have hdiam := (diameter_three_rank_five_of_ambient ambientRootOrbitsHyp).1
  have hk : ρ.ker = Subgroup.zpowers (cStab v) := ker_eq_zpowers_cStab hρ.2.1
  have hub := exists_dist_three_beta hρ
  obtain ⟨u, b, hvu, hbu, hρb⟩ := hub
  have hzex : ∃ zz : cgraph.neighborSet v, iv zz = ⟨rootInv, IsConj.refl _⟩ :=
    ⟨iv.symm _, iv.apply_symm_apply _⟩
  obtain ⟨zz, hzz⟩ := hzex
  have hvz : cgraph.Adj v zz := zz.2
  have hzS : clabelS zz ∈ vStab v :=
    (commute_clabelS_iff hinj v (clabelS zz)).1 (commute_clabelS_of_adj hvz).symm
  have hwex : ∃ w : vStab v, (w : Shat) = clabelS zz := ⟨⟨clabelS zz, hzS⟩, rfl⟩
  obtain ⟨w, hw⟩ := hwex
  have hρw : ρ w = rootStar := by
    rw [hρ.2.2.2.2 zz w (by rw [hw]; rfl), hzz]
    rfl
  have hρbw : Commute (ρ b) (ρ w) := by
    rw [hρb, hρw]
    exact commute_betaStarElt_rootStar
  have hbw : Commute b w := by
    rcases conj_eq_or_of_commute_map ρ hk (orderOf_cStab v) hρbw with h | h
    · exact commute_of_conj_eq h
    · exfalso
      have e := congrArg Subtype.val h
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hbu, hw,
        coe_cStab] at e
      have e1 : clabelS u * clabelS zz * (clabelS u)⁻¹ = clabelS (cvMul zz (clabelS u)⁻¹) := by
        rw [clabelS_cvMul, inv_inv]
      rw [e1] at e
      have r1 := rank_clabelS (cvMul zz (clabelS u)⁻¹)
      rw [e, rank_conj_shat (isConj_clabelS_mul_of_adj hvz), rank_xhatS] at r1
      omega
  have hcuz : Commute (clabelS u) (clabelS zz) := by
    have h := hbw.map (vStab v).subtype
    simp only [Subgroup.coe_subtype] at h
    rwa [hbu, hw] at h
  have huz : cgraph.dist u zz = 3 := by
    have hne : u ≠ zz := by
      intro e
      rw [e, SimpleGraph.dist_eq_one_iff_adj.2 hvz] at hvu
      omega
    rcases adj_or_dist_three_of_commute hdiam hne hcuz with h | h
    · exfalso
      have h1 := dist_le_add_one_of_adj (v := v) h.symm
      rw [SimpleGraph.dist_eq_one_iff_adj.2 hvz] at h1
      omega
    · exact h
  exact ⟨u, zz, b, w, hvu, hvz, huz, hbu, hw, hρb, hρw, hbw⟩

end Config

theorem exists_frame_conj
    {v u z : CVert} (hvu : cgraph.dist v u = 3) (hvz : cgraph.Adj v z)
    (hcuz : Commute (clabelS u) (clabelS z)) :
    ∃ g : Shat, g⁻¹ * clabelS v * g = sEquiv e2158 ∧ g⁻¹ * clabelS u * g = sEquiv (rs 6) ∧
      g⁻¹ * (clabelS v * clabelS z) * g = sEquiv xs := by
  have hfr := exists_frame
  obtain ⟨v₁, u₁, z₁, hv₁, hu₁, hz₁, hvu₁, hvz₁, hc₁⟩ := hfr
  have htr := exists_triple_cvMul hvu hvz hcuz hvu₁ hvz₁ hc₁
  obtain ⟨g, hgv, hgu, hgz⟩ := htr
  have hgv' : g⁻¹ * clabelS v * g = sEquiv e2158 := by rw [← clabelS_cvMul, hgv, hv₁]
  have hgz' : g⁻¹ * clabelS z * g = sEquiv (e2158 * xs) := by rw [← clabelS_cvMul, hgz, hz₁]
  refine ⟨g, hgv', by rw [← clabelS_cvMul, hgu, hu₁], ?_⟩
  calc g⁻¹ * (clabelS v * clabelS z) * g = (g⁻¹ * clabelS v * g) * (g⁻¹ * clabelS z * g) := by
        group
    _ = sEquiv xs := by rw [hgv', hgz', sEquiv_e2158_mul_e2158_xs]

theorem rank_outer_triple
    {v u z : CVert} (hvu : cgraph.dist v u = 3) (hvz : cgraph.Adj v z)
    (hcuz : Commute (clabelS u) (clabelS z)) :
    ((βr (sEquiv.symm (clabelS u * (clabelS v * clabelS z)))) - 1).rank = 2168 := by
  obtain ⟨g, -, hgu, hgx⟩ := exists_frame_conj hvu hvz hcuz
  have hconj : IsConj (clabelS u * (clabelS v * clabelS z)) (sEquiv (rs 6 * xs)) := by
    refine isConj_iff.2 ⟨g⁻¹, ?_⟩
    calc g⁻¹ * (clabelS u * (clabelS v * clabelS z)) * g⁻¹⁻¹ =
          (g⁻¹ * clabelS u * g) * (g⁻¹ * (clabelS v * clabelS z) * g) := by group
      _ = sEquiv (rs 6 * xs) := by rw [hgu, hgx, map_mul]
  rw [rank_conj_shat hconj, MulEquiv.symm_apply_apply]
  exact rank_rs6_mul_xs

theorem clabelS_mul_mul_mul
    {v u z : CVert} (hcu : Commute (clabelS v) (clabelS u)) :
    clabelS v * (clabelS u * (clabelS v * clabelS z)) = clabelS u * clabelS z := by
  calc clabelS v * (clabelS u * (clabelS v * clabelS z)) =
        clabelS v * ((clabelS u * clabelS v) * clabelS z) := by rw [mul_assoc]
    _ = clabelS v * ((clabelS v * clabelS u) * clabelS z) := by rw [hcu.eq]
    _ = (clabelS v * clabelS v) * (clabelS u * clabelS z) := by group
    _ = clabelS u * clabelS z := by rw [clabelS_mul_clabelS, one_mul]

set_option maxHeartbeats 8000000 in
theorem native_H_outer_involution_classes
    {v : CVert} {ρ : vStab v →* GStar}
    {iv : cgraph.neighborSet v ≃ rootClass} (hρ : IsCompatLocal v ρ iv) :
    ∃ (u z : CVert) (b x : vStab v),
      cgraph.dist v u = 3 ∧ cgraph.Adj v z ∧ cgraph.dist u z = 3 ∧
      (b : Shat) = clabelS u ∧ (x : Shat) = clabelS v * clabelS z ∧
      IsConj (x : Shat) xhatS ∧ Commute b x ∧
      (∃ g : Shat, g⁻¹ * clabelS v * g = sEquiv e2158 ∧ g⁻¹ * (b : Shat) * g = sEquiv (rs 6) ∧
        g⁻¹ * (x : Shat) * g = sEquiv xs) ∧
      ρ b = betaStarElt ∧ ρ x = rootStar ∧
      {y : vStab v | ρ y = betaStarElt} = {b, cStab v * b} ∧
      {y : vStab v | ρ y = rootStar * betaStarElt} = {b * x, cStab v * (b * x)} ∧
      (∀ y : vStab v, IsConj (ρ y) betaStarElt ↔ IsConj y b ∨ IsConj y (cStab v * b)) ∧
      (∀ y : vStab v, IsConj (ρ y) (rootStar * betaStarElt) ↔
        IsConj y (b * x) ∨ IsConj y (cStab v * (b * x))) ∧
      orderOf b = 2 ∧ orderOf (cStab v * b) = 2 ∧ orderOf (b * x) = 2 ∧
      orderOf (cStab v * (b * x)) = 2 ∧
      ((βr (sEquiv.symm (b : Shat))) - 1).rank = 1860 ∧
      ((βr (sEquiv.symm ((cStab v * b : vStab v) : Shat))) - 1).rank = 2158 ∧
      ((βr (sEquiv.symm ((b * x : vStab v) : Shat))) - 1).rank = 2168 ∧
      ((βr (sEquiv.symm ((cStab v * (b * x) : vStab v) : Shat))) - 1).rank = 2158 ∧
      Nat.card (Subgroup.centralizer {b}) = 13244506413465600 ∧
      Nat.card (Subgroup.centralizer {cStab v * b}) = 13244506413465600 ∧
      Nat.card (Subgroup.centralizer {b * x}) = 190253629440 ∧
      Nat.card (Subgroup.centralizer {cStab v * (b * x)}) = 190253629440 ∧
      ¬ IsConj b (cStab v * b) ∧ ¬ IsConj (b * x) (cStab v * (b * x)) ∧
      ¬ IsConj (cStab v * b) (cStab v * (b * x)) := by
  have hcfg := exists_outer_config hρ
  obtain ⟨u, z, b, w, hvu, hvz, huz, hbu, hw, hρb, hρw, hbw⟩ := hcfg
  have hfin : Finite (vStab v) := Finite.of_injective _ Subtype.val_injective
  have hk : ρ.ker = Subgroup.zpowers (cStab v) := ker_eq_zpowers_cStab hρ.2.1
  have hc2 : orderOf (cStab v) = 2 := orderOf_cStab v
  have hcen : cStab v ∈ Subgroup.center (vStab v) := cStab_mem_center v
  have hcc : cStab v * cStab v = 1 := Subtype.ext (clabelS_mul_clabelS v)
  have hcuz : Commute (clabelS u) (clabelS z) := by
    have h := hbw.map (vStab v).subtype
    simp only [Subgroup.coe_subtype] at h
    rwa [hbu, hw] at h
  have hcu : Commute (clabelS v) (clabelS u) :=
    (labelsInput_of_ambient ambientRootOrbitsHyp v u hvu).2.2.2.symm
  have hρx : ρ (cStab v * w) = rootStar := by rw [map_mul_of_ker ρ hk, hρw]
  have hxS : ((cStab v * w : vStab v) : Shat) = clabelS v * clabelS z := by
    rw [Subgroup.coe_mul, coe_cStab, hw]
  have hbc : Commute b (cStab v) := Subgroup.mem_center_iff.1 hcen b
  have hcw : Commute (cStab v) w := (Subgroup.mem_center_iff.1 hcen w).symm
  have hbx : Commute b (cStab v * w) := hbc.mul_right hbw
  have hrb : ((βr (sEquiv.symm (b : Shat))) - 1).rank = 1860 := by
    rw [hbu]
    exact rank_clabelS u
  have hrcb : ((βr (sEquiv.symm ((cStab v * b : vStab v) : Shat))) - 1).rank = 2158 := by
    rw [Subgroup.coe_mul, coe_cStab, hbu]
    exact rank_clabelS_mul_of_dist_three hvu
  have hrbx : ((βr (sEquiv.symm ((b * (cStab v * w) : vStab v) : Shat))) - 1).rank = 2168 := by
    rw [Subgroup.coe_mul, hxS, hbu]
    exact rank_outer_triple hvu hvz hcuz
  have hrcbx : ((βr (sEquiv.symm ((cStab v * (b * (cStab v * w)) : vStab v) : Shat))) -
      1).rank = 2158 := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hxS, coe_cStab, hbu, clabelS_mul_mul_mul hcu]
    exact rank_clabelS_mul_of_dist_three huz
  have hn1 : ¬ IsConj b (cStab v * b) := fun h => by
    have e := rank_conj_shat (coe_isConj h)
    rw [hrb, hrcb] at e
    omega
  have hn2 : ¬ IsConj (b * (cStab v * w)) (cStab v * (b * (cStab v * w))) := fun h => by
    have e := rank_conj_shat (coe_isConj h)
    rw [hrbx, hrcbx] at e
    omega
  have hρbx : ρ (b * (cStab v * w)) = rootStar * betaStarElt := by
    rw [map_mul, hρb, hρx]
    exact commute_betaStarElt_rootStar.eq
  have hbb : b * b = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hbu, Subgroup.coe_one]
    exact clabelS_mul_clabelS u
  have hww : w * w = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hw, Subgroup.coe_one]
    exact clabelS_mul_clabelS z
  have hxx : cStab v * w * (cStab v * w) = 1 := mul_self_mul_of_commute hcw hcc hww
  have hβ1 : betaStarElt ≠ 1 := fun h => by
    have := CFSG.Monster.B.E6.FieldInvF4.orderOf_betaStarElt
    rw [h, orderOf_one] at this
    omega
  have ht1 : rootStar * betaStarElt ≠ 1 := fun h => by
    have := CFSG.Monster.B.E6.FieldInvF4.orderOf_tStar
    rw [show CFSG.Monster.B.E6.FieldInvF4.tStar = rootStar * betaStarElt from rfl, h,
      orderOf_one] at this
    omega
  have hG := outer_fibres_of ρ hρ.1 hcen hk hc2 hbx hρb hρbx hbb hxx hβ1 ht1 hn1 hn2
    not_isConj_betaStarElt_tStar
  have hC := CFSG.Monster.B.E6.FieldInvF4.card_centralizer_betaStarElt
  have hCt : Nat.card (Subgroup.centralizer {rootStar * betaStarElt}) = 95126814720 :=
    CFSG.Monster.B.E6.FieldInvF4.card_centralizer_tStar
  have hfr := exists_frame_conj hvu hvz hcuz
  obtain ⟨g, hgv, hgu, hgx⟩ := hfr
  refine ⟨u, z, b, cStab v * w, hvu, hvz, huz, hbu, hxS,
    by rw [hxS]; exact isConj_clabelS_mul_of_adj hvz, hbx,
    ⟨g, hgv, by rw [hbu]; exact hgu, by rw [hxS]; exact hgx⟩, hρb, hρx, hG.1, hG.2.1, hG.2.2.1,
    hG.2.2.2.1, hG.2.2.2.2.1, hG.2.2.2.2.2.1, hG.2.2.2.2.2.2.1, hG.2.2.2.2.2.2.2.1, hrb, hrcb,
    hrbx, hrcbx, ?_, ?_, ?_, ?_, hn1, hn2, hG.2.2.2.2.2.2.2.2.2.2.2.2⟩
  · rw [hG.2.2.2.2.2.2.2.2.1, hC]
  · rw [hG.2.2.2.2.2.2.2.2.2.1, hC]
  · rw [hG.2.2.2.2.2.2.2.2.2.2.1, hCt]
  · rw [hG.2.2.2.2.2.2.2.2.2.2.2.1, hCt]

end CFSG.Monster.B.CTIB

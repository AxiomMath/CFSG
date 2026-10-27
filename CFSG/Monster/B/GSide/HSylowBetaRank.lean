module

public import CFSG.Monster.B.GSide.HSylowBetaClasses
public import CFSG.Monster.B.GSide.HSylowBetaCert
public import CFSG.Monster.B.GSide.HInnerFusion
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
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3137
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
public import Certificates.Certificate3951
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

open MulOpposite CFSG.Blueprint CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam
open CFSG.Monster.B.CTIB (Qs xs qS rs e2158 sEquiv)
open scoped commutatorElement

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

section Generic

variable {G : Type*} [Group G]

theorem commute_of_commutator_mul_self {b m : G} (hb : b * b = 1)
    (hz : (b⁻¹ * m⁻¹ * b * m) * (b⁻¹ * m⁻¹ * b * m) = 1) : Commute b (b⁻¹ * m⁻¹ * b * m) := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hc2 : (m⁻¹ * b * m) * (m⁻¹ * b * m) = 1 := by
    calc (m⁻¹ * b * m) * (m⁻¹ * b * m) = m⁻¹ * (b * b) * m := by group
      _ = 1 := by rw [hb]; group
  have hcinv : (m⁻¹ * b * m)⁻¹ = m⁻¹ * b * m := inv_eq_of_mul_eq_one_right hc2
  have e : b⁻¹ * m⁻¹ * b * m = b * (m⁻¹ * b * m) := by rw [hbinv]; group
  rw [e] at hz ⊢
  have hcb : (m⁻¹ * b * m) * b = b * (m⁻¹ * b * m) := by
    have h := inv_eq_of_mul_eq_one_right hz
    rwa [mul_inv_rev, hbinv, hcinv] at h
  show b * (b * (m⁻¹ * b * m)) = b * (m⁻¹ * b * m) * b
  rw [mul_assoc b (m⁻¹ * b * m) b, hcb]

theorem eq_of_natCard_le_four {K : Subgroup G} [Finite K] (hK : Nat.card K ≤ 4) {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hab1 : a * b ≠ 1)
    {f : G} (hf : f ∈ K) : f = 1 ∨ f = a ∨ f = b ∨ f = a * b := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hsub : ({f, 1, a, b, a * b} : Set G) ⊆ K := by
    rintro x (rfl | rfl | rfl | rfl | rfl)
    · exact hf
    · exact K.one_mem
    · exact ha
    · exact hb
    · exact K.mul_mem ha hb
  have hab2 : a * b ≠ a := fun h => hb1 (by simpa using h)
  have hab3 : a * b ≠ b := fun h => ha1 (by simpa using h)
  have hcard : ({f, 1, a, b, a * b} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [h1, h2, h3, h4]),
      Set.ncard_insert_of_notMem (by simp [ha1.symm, hb1.symm, hab1.symm]),
      Set.ncard_insert_of_notMem (by simp [hab, hab2.symm]),
      Set.ncard_insert_of_notMem (by simp [hab3.symm]), Set.ncard_singleton]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard, ← Nat.card_coe_set_eq] at hle
  have : Nat.card (K : Set G) = Nat.card K := rfl
  omega

theorem mem_closure_pair_cases {c β : G} (hc : c * c = 1) (hβ : β * β = 1) (hcβ : c * β = β * c)
    {v : G} (hv : v ∈ Subgroup.closure ({c, β} : Set G)) :
    v = 1 ∨ v = c ∨ v = β ∨ v = c * β := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have hβinv : β⁻¹ = β := inv_eq_of_mul_eq_one_right hβ
  have key : ∀ x y : G, (x = 1 ∨ x = c ∨ x = β ∨ x = c * β) →
      (y = 1 ∨ y = c ∨ y = β ∨ y = c * β) → (x * y = 1 ∨ x * y = c ∨ x * y = β ∨
        x * y = c * β) := by
    have e1 : c * (c * β) = β := by rw [← mul_assoc, hc, one_mul]
    have e2 : β * (c * β) = c := by rw [← mul_assoc, ← hcβ, mul_assoc, hβ, mul_one]
    have e3 : c * β * c = β := by rw [hcβ, mul_assoc, hc, mul_one]
    have e4 : c * β * β = c := by rw [mul_assoc, hβ, mul_one]
    have e5 : c * β * (c * β) = 1 := by rw [← mul_assoc, e3, hβ]
    intro x y hx hy
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp only [one_mul, mul_one, hc, hβ, e1, e2, e3, e4, e5, hcβ.symm, true_or, or_true]
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy => exact key x y hx hy
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl hcinv)
    · exact Or.inr (Or.inr (Or.inl hβinv))
    · right; right; right
      rw [mul_inv_rev, hcinv, hβinv, hcβ]

end Generic

section Ranks

theorem rank_isConj_eq
    {s t : Shat} (h : IsConj s t) :
    ((βr (sEquiv.symm s)) - 1).rank = ((βr (sEquiv.symm t)) - 1).rank :=
  CTIB.rank_conj_shat h

theorem rkH_eq_of_coe
    {y : vStab cv0} {s : Shat} (h : (y : Shat) = s) :
    rkH y = ((βr (sEquiv.symm s)) - 1).rank := by
  rw [rkH, h]

private theorem rkH_one_eq :
    rkH 1 = 0 := by
  rw [rkH, Subgroup.coe_one, map_one]
  exact CTIB.rank_beta_one

theorem rkH_label
    {y : vStab cv0} {p : CVert} (h : (y : Shat) = clabelS p) : rkH y = 1860 := by
  rw [rkH_eq_of_coe h]
  exact CTIB.rank_clabelS p

theorem rkH_adj
    {y : vStab cv0} {p q : CVert} (hpq : cgraph.Adj p q)
    (h : (y : Shat) = clabelS p * clabelS q) : rkH y = 2048 := by
  rw [rkH_eq_of_coe h, rank_isConj_eq (CTIB.isConj_clabelS_mul_of_adj hpq)]
  exact CTIB.rank_xhatS

end Ranks

section FourGroup

variable {u : CVert} {β : vStab cv0} {X : Subgroup (vStab cv0)}

theorem exists_hc5_ab
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) :
    ∃ (w w' : CVert) (a b : vStab cv0),
      cgraph.Adj cv0 w ∧ cgraph.dist u w = 3 ∧ Commute (clabelS u) (clabelS w) ∧
      cgraph.Adj u w' ∧ cgraph.dist cv0 w' = 3 ∧ Commute (clabelS cv0) (clabelS w') ∧
      a ∈ hc5ZP u X ∧ (a : Shat) = clabelS cv0 * clabelS w ∧
      b ∈ hc5ZP u X ∧ (b : Shat) = clabelS u * clabelS w' ∧
      rkH a = 2048 ∧ rkH (cV0 * a) = 1860 ∧ rkH b = 2048 ∧ rkH (cV0 * b) = 2168 := by
  obtain ⟨w, hw, hdw, hcw, a, ha, hae⟩ := exists_hc5ZP_Ev hvu hβ hXβ hX
  obtain ⟨w', hw', hdw', hcw', b, hb, hbe⟩ := exists_hc5ZP_Eu hvu hβ hXβ hX
  refine ⟨w, w', a, b, hw, hdw, hcw, hw', hdw', hcw', ha, hae, hb, hbe, rkH_adj hw hae, ?_,
    rkH_adj hw' hbe, ?_⟩
  · refine rkH_label (p := w) ?_
    rw [Subgroup.coe_mul, hae, coe_cV0, ← mul_assoc, clabelS_mul_clabelS, one_mul]
  · have huv : cgraph.dist u cv0 = 3 := by rw [SimpleGraph.dist_comm]; exact hvu
    rw [rkH_eq_of_coe (show ((cV0 * b : vStab cv0) : Shat) =
      clabelS cv0 * (clabelS u * clabelS w') by rw [Subgroup.coe_mul, hbe, coe_cV0])]
    exact CTIB.rank_outer_triple huv hw' hcw'

theorem hc5ZP_cases
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) {a b : vStab cv0}
    (ha : a ∈ hc5ZP u X) (hb : b ∈ hc5ZP u X) (hra : rkH a = 2048) (hrb : rkH b = 2048)
    (hrca : rkH (cV0 * a) = 1860) (hrcb : rkH (cV0 * b) = 2168) (hbb : b * b = 1)
    {f : vStab cv0} (hf : f ∈ hc5ZP u X) : f = 1 ∨ f = a ∨ f = b ∨ f = a * b := by
  have ha1 : a ≠ 1 := fun h => by rw [h, rkH_one_eq] at hra; exact absurd hra (by norm_num)
  have hb1 : b ≠ 1 := fun h => by rw [h, rkH_one_eq] at hrb; exact absurd hrb (by norm_num)
  have hab : a ≠ b := fun h => by rw [h, hrcb] at hrca; exact absurd hrca (by norm_num)
  have hab1 : a * b ≠ 1 := fun h => hab (by
    rw [mul_eq_one_iff_eq_inv] at h
    rw [h, inv_eq_of_mul_eq_one_right hbb])
  exact eq_of_natCard_le_four (hc5ZP_facts hvu hβ hXβ hX).1 ha hb ha1 hb1 hab hab1 hf

end FourGroup

section Frame

@[expose] def hc5Iota (g : Shat) : Sbp →* Shat :=
  (MulAut.conj g).toMonoidHom.comp sEquiv.toMonoidHom

theorem hc5Iota_apply (g : Shat) (s : Sbp) : hc5Iota g s = g * sEquiv s * g⁻¹ := rfl

theorem hc5Iota_injective (g : Shat) : Function.Injective (hc5Iota g) :=
  (MulAut.conj g).injective.comp sEquiv.injective

theorem rank_hc5Iota
    (g : Shat) (s : Sbp) :
    ((βr (sEquiv.symm (hc5Iota g s))) - 1).rank = ((βr s) - 1).rank := by
  rw [hc5Iota_apply, ← rank_isConj_eq (isConj_iff.2 ⟨g, rfl⟩), MulEquiv.symm_apply_apply]

theorem hc5Iota_commute_iff (g : Shat) {s t : Sbp} :
    hc5Iota g s * hc5Iota g t = hc5Iota g t * hc5Iota g s ↔ s * t = t * s := by
  rw [← map_mul, ← map_mul, (hc5Iota_injective g).eq_iff]

@[expose] def hc5T :
    Set Sbp :=
  {s | ∃ n ∈ Qs, n * e2158 = e2158 * n ∧ (rs 6)⁻¹ * n⁻¹ * rs 6 * n = s}

theorem ncard_hc5T :
    (hc5T \ {1}).ncard = 63 := by
  rw [hc5T, hc5_set_eq]
  exact ncard_hc5_set

theorem conj_mem_hc5T
    {t : Sbp} (hte : Commute t e2158) (htr : Commute t (rs 6))
    (htx : t * xs = xs * t) {s : Sbp} (hs : s ∈ hc5T \ {1}) : t * s * t⁻¹ ∈ hc5T \ {1} := by
  obtain ⟨⟨n, hn, hne, rfl⟩, h1⟩ := hs
  have hJ : (t⁻¹).unop ∈ CFSG.Monster.B.Jbar := by
    rw [unop_inv]
    refine CFSG.Monster.B.Jbar.inv_mem (CFSG.Monster.B.mem_Jbar_iff_comm.2 ?_)
    have h := congrArg MulOpposite.unop htx
    rw [unop_mul, unop_mul] at h
    exact h
  have hnQ : t * n * t⁻¹ ∈ Qs := by
    have h := CTIB.conj_mem_Qs hJ hn
    rwa [inv_inv] at h
  have hc : Commute (t * n * t⁻¹) e2158 := (hte.mul_left hne).mul_left hte.inv_left
  have h2 : t⁻¹ * rs 6 * t = rs 6 := by rw [mul_assoc, ← htr.eq, inv_mul_cancel_left]
  have h3 : (rs 6)⁻¹ * t = t * (rs 6)⁻¹ := htr.inv_right.eq.symm
  refine ⟨⟨t * n * t⁻¹, hnQ, hc.eq, ?_⟩, ?_⟩
  · calc (rs 6)⁻¹ * (t * n * t⁻¹)⁻¹ * rs 6 * (t * n * t⁻¹) =
        (rs 6)⁻¹ * t * n⁻¹ * (t⁻¹ * rs 6 * t) * n * t⁻¹ := by group
      _ = (rs 6)⁻¹ * t * n⁻¹ * rs 6 * n * t⁻¹ := by rw [h2]
      _ = t * (rs 6)⁻¹ * n⁻¹ * rs 6 * n * t⁻¹ := by rw [h3]
      _ = t * ((rs 6)⁻¹ * n⁻¹ * rs 6 * n) * t⁻¹ := by group
  · intro h
    apply h1
    have h' : t * ((rs 6)⁻¹ * n⁻¹ * rs 6 * n) * t⁻¹ = 1 := h
    rwa [mul_inv_eq_one, mul_eq_left] at h'

end Frame

section Fixed

variable {u : CVert} {β : vStab cv0} {X : Subgroup (vStab cv0)}

theorem beta_not_mem_commutator
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u) :
    β ∉ commutator (vStab cv0) := by
  have h := native_distance_three_label_is_outer_local_involution_final
    (mem_sphereDistThree.2 hvu)
  exact h.2.1 β hβ

theorem cV0_mem_commutator :
    cV0 ∈ commutator (vStab cv0) :=
  (coe_mem_derivedStab_iff cV0).1 (clabelS_mem_derivedStab_self' cv0)

theorem mem_commutator_of_mem_hc5F {f : vStab cv0} (hf : f ∈ hc5F u) :
    f ∈ commutator (vStab cv0) :=
  (coe_mem_derivedStab_iff f).1 (pairF4_le_derivedStab cv0 u (mem_hc5F.1 hf))

theorem exists_hc5Iota
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u) {w : CVert}
    (hw : cgraph.Adj cv0 w) (hcw : Commute (clabelS u) (clabelS w)) {a : vStab cv0}
    (hae : (a : Shat) = clabelS cv0 * clabelS w) :
    ∃ g : Shat, hc5Iota g e2158 = cV0 ∧ hc5Iota g (rs 6) = β ∧ hc5Iota g xs = a := by
  obtain ⟨g, hgc, hgβ, hga⟩ := CTIB.exists_frame_conj hvu hw hcw
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [hc5Iota_apply, ← hgc, coe_cV0]
    group
  · rw [hc5Iota_apply, ← hgβ, hβ]
    group
  · rw [hc5Iota_apply, ← hga, hae]
    group

theorem conj_mem_image_hc5T
    {g : Shat} {a : vStab cv0} (hιe : hc5Iota g e2158 = cV0)
    (hιr : hc5Iota g (rs 6) = β) (hιx : hc5Iota g xs = a) {x₀ : vStab cv0}
    (hxc : (x₀ : Shat) * cV0 = cV0 * x₀) (hxβ : (x₀ : Shat) * β = β * x₀)
    (hxa : (x₀ : Shat) * a = a * x₀) {s : Sbp} (hs : s ∈ hc5T \ {1}) :
    (x₀ : Shat) * hc5Iota g s * (x₀ : Shat)⁻¹ ∈ hc5Iota g '' (hc5T \ {1}) := by
  obtain ⟨t, hιt⟩ : ∃ t : Sbp, hc5Iota g t = x₀ :=
    ⟨sEquiv.symm (g⁻¹ * (x₀ : Shat) * g), by rw [hc5Iota_apply, MulEquiv.apply_symm_apply]; group⟩
  have hte : Commute t e2158 := (hc5Iota_commute_iff g).1 (by rw [hιt, hιe]; exact hxc)
  have htr : Commute t (rs 6) := (hc5Iota_commute_iff g).1 (by rw [hιt, hιr]; exact hxβ)
  have htx : t * xs = xs * t := (hc5Iota_commute_iff g).1 (by rw [hιt, hιx]; exact hxa)
  refine ⟨t * s * t⁻¹, conj_mem_hc5T hte htr htx hs, ?_⟩
  rw [map_mul (hc5Iota g), map_mul (hc5Iota g), map_inv (hc5Iota g), hιt]

theorem exists_elem_of_mem_hc5T
    (hβ : (β : Shat) = clabelS u) {g : Shat} {a : vStab cv0}
    (hιe : hc5Iota g e2158 = cV0) (hιr : hc5Iota g (rs 6) = β) (hιx : hc5Iota g xs = a)
    {s : Sbp} (hs : s ∈ hc5T \ {1}) :
    ∃ z : vStab cv0, (z : Shat) = hc5Iota g s ∧ z ≠ 1 ∧ z * z = 1 ∧ Commute β z ∧
      z ∈ commutator (vStab cv0) ∧ rkH z = 2048 ∧ rkH (a * z) = 2048 ∧
      rkH (cV0 * z) = 2168 ∧ rkH (cV0 * (a * z)) = 2168 := by
  obtain ⟨⟨n, hn, hne, hsn⟩, hs1⟩ := hs
  have h1 := hc5_commutator_mem hn hne
  obtain ⟨z₀, hz₀, hsz⟩ := h1
  rw [hsn] at hsz
  have hz₀0 : z₀ ≠ 0 := fun h => hs1 (by rw [hsz, h, CTIB.qS_zero]; rfl)
  have h2 := hc5_ranks hz₀ hz₀0
  obtain ⟨-, hsq, hr1, hr2, hr3, hr4⟩ := h2
  have hιs : hc5Iota g s = (β : Shat)⁻¹ * (hc5Iota g n)⁻¹ * β * hc5Iota g n := by
    subst hsn
    simp only [map_mul, map_inv, hιr]
  have hm : hc5Iota g n ∈ vStab cv0 := by
    refine (commute_clabelS_iff' cv0 _).1 ?_
    have h : hc5Iota g (n * e2158) = hc5Iota g (e2158 * n) := by rw [hne]
    simp only [map_mul, hιe, coe_cV0] at h
    exact h
  have hmem : hc5Iota g s ∈ vStab cv0 := by
    rw [hιs]
    exact (vStab cv0).mul_mem ((vStab cv0).mul_mem ((vStab cv0).mul_mem
      ((vStab cv0).inv_mem β.2) ((vStab cv0).inv_mem hm)) β.2) hm
  have hss : hc5Iota g s * hc5Iota g s = 1 := by
    rw [← map_mul, hsz, hsq, map_one]
  have hcomm : Commute (β : Shat) (hc5Iota g s) := by
    rw [hιs] at hss ⊢
    have hββ : (β : Shat) * β = 1 := by rw [← Subgroup.coe_mul, beta_mul_self hβ, Subgroup.coe_one]
    exact commute_of_commutator_mul_self hββ hss
  refine ⟨⟨_, hmem⟩, rfl, fun h => hs1 ?_, Subtype.ext hss, Subtype.ext hcomm.eq, ?_, ?_, ?_, ?_,
    ?_⟩
  · apply hc5Iota_injective g
    rw [map_one]
    exact congrArg Subtype.val h
  · have e : (⟨_, hmem⟩ : vStab cv0) = ⁅β⁻¹, (⟨_, hm⟩ : vStab cv0)⁻¹⁆ := Subtype.ext (by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      exact hιs)
    rw [e, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · rw [rkH_eq_of_coe (rfl : ((⟨_, hmem⟩ : vStab cv0) : Shat) = hc5Iota g s), rank_hc5Iota,
      hsz]
    exact hr1
  · have e : ((a * ⟨_, hmem⟩ : vStab cv0) : Shat) = hc5Iota g (xs * qS z₀) := by
      rw [← hsz]
      simp only [Subgroup.coe_mul, map_mul, hιx]
    rw [rkH_eq_of_coe e, rank_hc5Iota]
    exact hr2
  · have e : ((cV0 * ⟨_, hmem⟩ : vStab cv0) : Shat) = hc5Iota g (e2158 * qS z₀) := by
      rw [← hsz]
      simp only [Subgroup.coe_mul, map_mul, hιe]
    rw [rkH_eq_of_coe e, rank_hc5Iota]
    exact hr3
  · have e : ((cV0 * (a * ⟨_, hmem⟩) : vStab cv0) : Shat) =
        hc5Iota g (e2158 * (xs * qS z₀)) := by
      rw [← hsz]
      simp only [Subgroup.coe_mul, map_mul, hιe, hιx]
    rw [rkH_eq_of_coe e, rank_hc5Iota]
    exact hr4

theorem exists_fixed_rank
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) {w : CVert}
    (hw : cgraph.Adj cv0 w) (hcw : Commute (clabelS u) (clabelS w)) {a : vStab cv0}
    (ha : a ∈ hc5ZP u X) (hae : (a : Shat) = clabelS cv0 * clabelS w) :
    ∃ z : vStab cv0, z ≠ 1 ∧ (z ∈ X ∧ ∀ y ∈ X, z * y = y * z) ∧
      z ∈ commutator (vStab cv0) ∧ rkH z = 2048 ∧ rkH (a * z) = 2048 ∧
      rkH (cV0 * z) = 2168 ∧ rkH (cV0 * (a * z)) = 2168 := by
  have hg := exists_hc5Iota hvu hβ hw hcw hae
  obtain ⟨g, hιe, hιr, hιx⟩ := hg
  have haZ : ∀ y ∈ X, a * y = y * a :=
    ((mem_center_X_iff hvu hβ hXβ hX).2 ⟨a, ha, 1, Subgroup.one_mem _, (mul_one a).symm⟩).2
  have hinv : ∀ x ∈ X.map (vStab cv0).subtype, ∀ z ∈ hc5Iota g '' (hc5T \ {1}),
      x * z * x⁻¹ ∈ hc5Iota g '' (hc5T \ {1}) := by
    rintro x ⟨x₀, hx₀, rfl⟩ z ⟨s, hs, rfl⟩
    exact conj_mem_image_hc5T hιe hιr hιx
      (congrArg Subtype.val (Subgroup.mem_center_iff.1 cV0_mem_center_H x₀))
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 (hXβ hx₀)))
      (congrArg Subtype.val (haZ x₀ hx₀).symm) hs
  have hodd : Odd (hc5Iota g '' (hc5T \ {1})).ncard := by
    rw [Set.ncard_image_of_injective _ (hc5Iota_injective g), ncard_hc5T]
    decide
  have hfx := exists_conj_fixed_of_odd (isPGroup_map_X hX) (Set.toFinite _) hodd hinv
  obtain ⟨z, ⟨s, hs, rfl⟩, hfix⟩ := hfx
  have hel := exists_elem_of_mem_hc5T hβ hιe hιr hιx hs
  obtain ⟨zH, hzH, hz1, hzz, hβz, hzc, hr1, hr2, hr3, hr4⟩ := hel
  have hzX : ∀ y ∈ X, zH * y = y * zH := fun y hy => by
    have h := hfix y ⟨y, hy, rfl⟩
    rw [← hzH] at h
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    calc (zH : Shat) * y = ((y : Shat) * zH * (y : Shat)⁻¹) * y := by rw [h]
      _ = y * zH := by group
  exact ⟨zH, hz1, ⟨mem_X_of_commute hvu hβ hXβ hX
    (Subgroup.mem_centralizer_singleton_iff.2 hβz.eq.symm) hzz hzX, hzX⟩, hzc, hr1, hr2, hr3, hr4⟩

theorem rkH_mul_eq
    (hvu : cgraph.dist cv0 u = 3) (hβ : (β : Shat) = clabelS u)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hX : Nat.card X = 2 ^ 26) {w : CVert}
    (hw : cgraph.Adj cv0 w) (hcw : Commute (clabelS u) (clabelS w)) {a b : vStab cv0}
    (ha : a ∈ hc5ZP u X) (hae : (a : Shat) = clabelS cv0 * clabelS w) (haa : a * a = 1)
    (hZP : ∀ f ∈ hc5ZP u X, f = 1 ∨ f = a ∨ f = b ∨ f = a * b)
    (hrca : rkH (cV0 * a) = 1860) (hrcb : rkH (cV0 * b) = 2168) :
    rkH (a * b) = 2048 ∧ rkH (cV0 * (a * b)) = 2168 := by
  have h := exists_fixed_rank hvu hβ hXβ hX hw hcw ha hae
  obtain ⟨z, hz1, hzZ, hzc, hr1, hr2, hr3, hr4⟩ := h
  have hdec := (mem_center_X_iff hvu hβ hXβ hX).1 hzZ
  obtain ⟨f, hf, v, hv, hzfv⟩ := hdec
  have hcβ : cV0 * β = β * cV0 := (Subgroup.mem_center_iff.1 cV0_mem_center_H β).symm
  have hc : ∀ y : vStab cv0, y * cV0 = cV0 * y := fun y =>
    Subgroup.mem_center_iff.1 cV0_mem_center_H y
  have hfc : f ∈ commutator (vStab cv0) := mem_commutator_of_mem_hc5F (mem_hc5ZP.1 hf).1.2
  have hvc : v ∈ commutator (vStab cv0) := by
    have h1 := (commutator (vStab cv0)).mul_mem ((commutator (vStab cv0)).inv_mem hfc) hzc
    rwa [hzfv, inv_mul_cancel_left] at h1
  have hβc := beta_not_mem_commutator hvu hβ
  have hv' := mem_closure_pair_cases cV0_mul_self (beta_mul_self hβ) hcβ hv
  have hf' := hZP f hf
  rcases hv' with hv1 | hv1 | hv1 | hv1
  · rw [hv1, mul_one] at hzfv
    rw [hzfv] at hz1 hr1 hr2 hr3 hr4
    rcases hf' with hf1 | hf1 | hf1 | hf1
    · exact absurd hf1 hz1
    · rw [hf1, haa, rkH_one_eq] at hr2
      exact absurd hr2 (by norm_num)
    · rw [hf1] at hr2 hr4
      exact ⟨hr2, hr4⟩
    · rw [hf1] at hr1 hr3
      exact ⟨hr1, hr3⟩
  · rw [hv1] at hzfv
    rw [hzfv] at hr1 hr2
    rcases hf' with hf1 | hf1 | hf1 | hf1
    · rw [hf1, one_mul, rkH_cV0] at hr1
      exact absurd hr1 (by norm_num)
    · rw [hf1, hc a, hrca] at hr1
      exact absurd hr1 (by norm_num)
    · rw [hf1, hc b, hrcb] at hr1
      exact absurd hr1 (by norm_num)
    · have e : a * (a * b * cV0) = cV0 * b := by
        rw [← mul_assoc, ← mul_assoc, haa, one_mul, hc b]
      rw [hf1, e, hrcb] at hr2
      exact absurd hr2 (by norm_num)
  · rw [hv1] at hvc
    exact absurd hvc hβc
  · rw [hv1] at hvc
    have h1 := (commutator (vStab cv0)).mul_mem ((commutator (vStab cv0)).inv_mem
      cV0_mem_commutator) hvc
    rw [inv_mul_cancel_left] at h1
    exact absurd h1 hβc

end Fixed

end CFSG.Monster.B.GSide

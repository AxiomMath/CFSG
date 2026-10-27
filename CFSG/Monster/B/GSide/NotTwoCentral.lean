module

public import CFSG.Monster.B.Recog.GenericNotTwoCentral
public import CFSG.Monster.B.GSide.HSylowCenter
public import CFSG.Monster.B.GSide.CommutatorTest
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
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
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
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
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
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3013
public import Certificates.Certificate3027
public import Certificates.Certificate3044
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
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

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.Recog

@[expose] def centerInfCommutator {M : Type*} [Group M] (X : Subgroup M) : Subgroup M :=
  (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆

section Transport

variable {M N : Type*} [Group M] [Group N] {f : M →* N}

theorem map_center_map_subtype (hf : Function.Injective f) (X : Subgroup M) :
    ((Subgroup.center X).map X.subtype).map f =
      (Subgroup.center (X.map f)).map (X.map f).subtype := by
  let e : X ≃* X.map f := X.equivMapOfInjective f hf
  have hcomp : f.comp X.subtype = (X.map f).subtype.comp e.toMonoidHom := by
    ext x
    rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, ← Subgroup.map_center_eq e]
  rfl

theorem map_centerInfCommutator (hf : Function.Injective f) (X : Subgroup M) :
    (centerInfCommutator X).map f = centerInfCommutator (X.map f) := by
  rw [centerInfCommutator, centerInfCommutator, Subgroup.map_inf_eq _ _ f hf,
    Subgroup.map_commutator, map_center_map_subtype hf]

theorem map_centralizer_singleton (hf : Function.Injective f) (b : M) :
    (Subgroup.centralizer {b}).map f = f.range ⊓ Subgroup.centralizer {f b} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hx]
  · rintro ⟨⟨x, rfl⟩, hy⟩
    refine ⟨x, Subgroup.mem_centralizer_singleton_iff.2 (hf ?_), rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 hy

end Transport

theorem not_isConj_of_center_eq_four {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    {d r : G} (hZ : ((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype : Set G) =
      {1, d, r, d * r})
    (hr1 : r ≠ 1) (hrd : r ≠ d) (hdr : ¬ IsConj d (d * r)) : ¬ IsConj d r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmemZ : ∀ x : G, x ∈ ({1, d, r, d * r} : Set G) →
      x ∈ (P : Subgroup G) ∧ ∀ y ∈ (P : Subgroup G), x * y = y * x := by
    intro x hx
    rw [← hZ] at hx
    obtain ⟨⟨x, hxP⟩, hxc, rfl⟩ := hx
    exact ⟨hxP, fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.1 hxc ⟨y, hy⟩).symm⟩
  have hcent : ∀ x : G, x ∈ ({1, d, r, d * r} : Set G) →
      x ∈ Subgroup.centralizer (P : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => ((hmemZ x hx).2 y hy).symm
  have hd : d ∈ ({1, d, r, d * r} : Set G) := by simp
  have hr : r ∈ ({1, d, r, d * r} : Set G) := by simp
  intro hc
  obtain ⟨g, hg⟩ := isConj_iff.1 hc
  obtain ⟨n, hn, hn'⟩ := P.conj_eq_normalizer_conj_of_mem_centralizer d g⁻¹ (hcent d hd)
    (by rw [inv_inv, hg]; exact hcent r hr)
  rw [inv_inv, hg] at hn'
  have hm : n⁻¹ ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := Subgroup.inv_mem _ hn
  have hmd : n⁻¹ * d * n⁻¹⁻¹ = r := by rw [inv_inv, hn']
  obtain ⟨hmrP, hmrc⟩ := NotTwoCentral.conj_mem_center_of_mem_normalizer hm (hmemZ r hr).1
    (hmemZ r hr).2
  have hmrZ : n⁻¹ * r * n⁻¹⁻¹ ∈ ({1, d, r, d * r} : Set G) := by
    rw [← hZ]
    exact ⟨⟨_, hmrP⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext (hmrc y y.2).symm, rfl⟩
  rcases hmrZ with h | h | h | h
  · exact hr1 (by
      have := congrArg (fun x => n⁻¹⁻¹ * x * n⁻¹) h
      simpa [mul_assoc] using this)
  ·
    have hpow : ∀ k : ℕ, n⁻¹ ^ k * d * (n⁻¹ ^ k)⁻¹ = if Even k then d else r := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', mul_inv_rev, show n⁻¹ * n⁻¹ ^ k * d * ((n⁻¹ ^ k)⁻¹ * n⁻¹⁻¹) =
          n⁻¹ * (n⁻¹ ^ k * d * (n⁻¹ ^ k)⁻¹) * n⁻¹⁻¹ by group, ih]
        by_cases hk : Even k
        · rw [ite_eq_left hk, ite_eq_right (by simpa [Nat.even_add_one] using hk), hmd]
        · rw [ite_eq_right hk, ite_eq_left (by simpa [Nat.even_add_one] using hk), h]
    have hN := Subgroup.normal_in_normalizer (H := (P : Subgroup G))
    set q := ((P : Subgroup G).subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))).index
    have hqP : n⁻¹ ^ q ∈ (P : Subgroup G) := by
      have h1 := pow_card_eq_one' (G := Subgroup.normalizer ((P : Subgroup G) : Set G) ⧸
        (P : Subgroup G).subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G)))
        (x := QuotientGroup.mk ⟨n⁻¹, hm⟩)
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← Subgroup.index] at h1
      exact Subgroup.mem_subgroupOf.1 h1
    have hqodd : ¬ Even q := by
      intro he
      have hdvd : q ∣ (P : Subgroup G).index := by
        rw [← Subgroup.relIndex_mul_index (Subgroup.le_normalizer (H := (P : Subgroup G)))]
        exact dvd_mul_right _ _
      exact P.not_dvd_index ((even_iff_two_dvd.1 he).trans hdvd)
    have h2 := hpow q
    rw [ite_eq_right hqodd] at h2
    have h3 : n⁻¹ ^ q * d * (n⁻¹ ^ q)⁻¹ = d := by
      rw [← (hmemZ d hd).2 _ hqP, mul_inv_cancel_right]
    exact hrd (h2.symm.trans h3)
  · exact hrd (by
      have := congrArg (fun x => n⁻¹⁻¹ * x * n⁻¹) (h.trans hmd.symm)
      simpa [mul_assoc] using this)
  · exact hdr (hc.trans (isConj_iff.2 ⟨n⁻¹, h⟩))

theorem index_commutator_vStab_cv0 :
    (commutator (vStab cv0)).index = 2 := by
  have hmap : (commutator (vStab cv0)).map vStabEam.toMonoidHom = commutator Eam := by
    rw [commutator, commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ vStabEam.surjective]
  have h := Subgroup.index_map_eq (commutator (vStab cv0)) (f := vStabEam.toMonoidHom)
    vStabEam.surjective (by
      rw [(MonoidHom.ker_eq_bot_iff vStabEam.toMonoidHom).2 vStabEam.injective]
      exact bot_le)
  rw [hmap] at h
  rw [← h]
  exact CFSG.Monster.B.CTIB.derivedCoverInput_holds.1


section Iota

variable {G : Type*} [Group G] {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)

@[expose] def iotaPsi : vStab cv0 →* G :=
  (Subgroup.centralizer {d}).subtype.comp ψ.symm.toMonoidHom

theorem iotaPsi_apply (y : vStab cv0) :
    iotaPsi ψ y = ((ψ.symm y : Subgroup.centralizer {d}) : G) := rfl

theorem iotaPsi_injective : Function.Injective (iotaPsi ψ) :=
  (Subgroup.centralizer {d}).subtype_injective.comp ψ.symm.injective

theorem range_iotaPsi : (iotaPsi ψ).range = Subgroup.centralizer {d} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (ψ.symm y).2
  · intro hx
    refine ⟨ψ ⟨x, hx⟩, ?_⟩
    rw [iotaPsi_apply, MulEquiv.symm_apply_apply]

theorem map_top_iotaPsi :
    (⊤ : Subgroup (vStab cv0)).map (iotaPsi ψ) = Subgroup.centralizer {d} := by
  rw [← MonoidHom.range_eq_map, range_iotaPsi]

theorem iotaPsi_cV0 (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) :
    iotaPsi ψ cV0 = d := by
  rw [iotaPsi_apply, ← hψ, MulEquiv.symm_apply_apply]

theorem mem_dH_iff_iotaPsi (y : vStab cv0) : y ∈ dH ψ ↔ IsConj d (iotaPsi ψ y) := Iff.rfl

theorem inf_centralizer_iotaPsi (b : vStab cv0) :
    Subgroup.centralizer {d} ⊓ Subgroup.centralizer {iotaPsi ψ b} =
      (Subgroup.centralizer {b}).map (iotaPsi ψ) := by
  rw [map_centralizer_singleton (iotaPsi_injective ψ), range_iotaPsi]

theorem map_le_centralizer_iotaPsi (Y : Subgroup (vStab cv0)) :
    Y.map (iotaPsi ψ) ≤ Subgroup.centralizer {d} :=
  (Subgroup.map_le_range _ Y).trans (range_iotaPsi ψ).le

theorem relIndex_centralizer_iotaPsi (Y : Subgroup (vStab cv0)) :
    (Y.map (iotaPsi ψ)).relIndex (Subgroup.centralizer {d}) = Y.index := by
  rw [← map_top_iotaPsi ψ, Subgroup.relIndex_map_map_of_injective _ _ (iotaPsi_injective ψ),
    Subgroup.relIndex_top_right]

end Iota

theorem image_four_gen {M N : Type*} [Group M] [Group N] (f : M →* N) {c : M} {d : N}
    (hc : f c = d) (r : M) : f '' ({1, c, r, c * r} : Set M) = {1, d, f r, d * f r} := by
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, map_one,
    map_mul, hc]

section RA

variable {G : Type*} [Group G] {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
  (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0)

include hψ in
theorem center_map_iotaPsi {T : Subgroup (vStab cv0)} {r : vStab cv0}
    (hZT : ((Subgroup.center T).map T.subtype : Set (vStab cv0)) = {1, cV0, r, cV0 * r}) :
    ((Subgroup.center (T.map (iotaPsi ψ))).map (T.map (iotaPsi ψ)).subtype : Set G) =
      {1, d, iotaPsi ψ r, d * iotaPsi ψ r} := by
  rw [← map_center_map_subtype (iotaPsi_injective ψ), Subgroup.coe_map, hZT,
    image_four_gen _ (iotaPsi_cV0 ψ hψ)]

theorem iotaPsi_ne_one_of_mem_RA
    {r : vStab cv0} (hr : r ∈ RA) : iotaPsi ψ r ≠ 1 := by
  intro h
  obtain ⟨w, -, hw⟩ := hr
  have h1 : r = 1 := iotaPsi_injective ψ (h.trans (map_one _).symm)
  have h2 := orderOf_clabelS w
  rw [← hw, h1] at h2
  simp at h2

include hψ in
theorem iotaPsi_ne_of_mem_RA
    {r : vStab cv0} (hr : r ∈ RA) : iotaPsi ψ r ≠ d := fun h =>
  cV0_not_mem_RA (by
    rw [← iotaPsi_injective ψ (h.trans (iotaPsi_cV0 ψ hψ).symm)]
    exact hr)

include hψ in
theorem not_isConj_mul_of_mem_RA
    {r : vStab cv0} (hr : r ∈ RA) :
    ¬ IsConj d (d * iotaPsi ψ r) := by
  have e : d * iotaPsi ψ r = iotaPsi ψ (cV0 * r) := by
    rw [map_mul, iotaPsi_cV0 ψ hψ]
  rw [e, ← mem_dH_iff_iotaPsi]
  exact not_mem_dH_of_mem_RB' ψ hψ (by
    show cV0 * (cV0 * r) ∈ RA
    rw [← mul_assoc, cV0_mul_self, one_mul]
    exact hr)

end RA

theorem not_mem_dH_of_mem_RA_of_sylow
    {G : Type*} [Group G] [Finite G] {d : G}
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (T : Sylow 2 (vStab cv0))
    (hTsyl : ¬ 2 ∣ ((T : Subgroup (vStab cv0)).map (iotaPsi ψ)).index) {y : vStab cv0}
    (hy : y ∈ RA) : y ∉ dH ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, r, hr, hZT⟩ := native_H_sylow_two_center T
  have hZP := center_map_iotaPsi ψ hψ hZT
  rw [← IsPGroup.toSylow_coe (T.isPGroup'.map (iotaPsi ψ)) hTsyl] at hZP
  have hrD := not_isConj_of_center_eq_four _ hZP (iotaPsi_ne_one_of_mem_RA ψ hr)
    (iotaPsi_ne_of_mem_RA ψ hψ hr) (not_isConj_mul_of_mem_RA ψ hψ hr)
  intro hyD
  exact hrD ((mem_dH_iff_iotaPsi ψ r).1 (mem_dH_of_isConj ψ hyD (RA_isConj y r hy hr)))

section Hyp

theorem map_inv_mul_gen {M N : Type*} [Group M] [Group N] (f : M →* N) {c : M} {d : N}
    (hc : f c = d) (z : M) : f (c⁻¹ * z) = d⁻¹ * f z := by
  rw [map_mul, map_inv, hc]

theorem map_mul_inv_mul_gen {M N : Type*} [Group M] [Group N] (f : M →* N) {c : M} {d : N}
    (hc : f c = d) (b z : M) : f ((c * b)⁻¹ * z) = (d * f b)⁻¹ * f z := by
  rw [map_mul, map_inv, map_mul, hc]

theorem map_inv_mul_gen' {M N : Type*} [Group M] [Group N] (f : M →* N) {c : M} {d : N}
    (hc : f c = d) (b : M) : f (b⁻¹ * c) = (f b)⁻¹ * d := by
  rw [map_mul, map_inv, hc]

theorem map_inv_mul_gen'' {M N : Type*} [Group M] [Group N] (f : M →* N) (b z : M) :
    f (b⁻¹ * z) = (f b)⁻¹ * f z := by
  rw [map_mul, map_inv]

theorem mul_self_of_isConj_gen {M N : Type*} [Group M] [Group N] {f : M →* N}
    (hf : Function.Injective f) {b u : M} (hb : b ^ 2 = 1) (h : IsConj (f b) (f u)) :
    u * u = 1 := by
  have h2 := h.pow 2
  rw [← map_pow, hb, map_one, isConj_one_right, ← map_pow] at h2
  rw [← sq]
  exact hf (h2.trans (map_one f).symm)

theorem map_sq_eq_one_gen {M N : Type*} [Group M] [Group N] (f : M →* N) {b : M}
    (hb : b ^ 2 = 1) : f b ^ 2 = 1 := by
  rw [← map_pow, hb, map_one]

theorem map_le_centralizer_gen {M N : Type*} [Group M] [Group N] (f : M →* N) {X : Subgroup M}
    {b : M} (hX : X ≤ Subgroup.centralizer {b}) : X.map f ≤ Subgroup.centralizer {f b} := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    Subgroup.mem_centralizer_singleton_iff.1 (hX hx)]

theorem map_mul_gen {M N : Type*} [Group M] [Group N] (f : M →* N) {c : M} {d : N}
    (hc : f c = d) (u : M) : f (c * u) = d * f u := by
  rw [map_mul, hc]

theorem map_mul_mul_gen {M N : Type*} [Group M] [Group N] (f : M →* N) {c : M} {d : N}
    (hc : f c = d) (b u : M) : f (c * b * u) = d * f b * f u := by
  rw [map_mul, map_mul, hc]

variable {G : Type*} [Group G] {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
  (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0)

include hψ in
theorem hZ_iotaPsi {X : Subgroup (vStab cv0)} {β : vStab cv0}
    (hZ : ∀ z ∈ X, (∀ y ∈ X, z * y = y * z) → z ∈ centerInfCommutator X ∨
      cV0⁻¹ * z ∈ centerInfCommutator X ∨ β⁻¹ * z ∈ centerInfCommutator X ∨
      (cV0 * β)⁻¹ * z ∈ centerInfCommutator X) :
    ∀ z ∈ X.map (iotaPsi ψ), (∀ y ∈ X.map (iotaPsi ψ), z * y = y * z) →
      z ∈ (centerInfCommutator X).map (iotaPsi ψ) ∨
        d⁻¹ * z ∈ (centerInfCommutator X).map (iotaPsi ψ) ∨
        (iotaPsi ψ β)⁻¹ * z ∈ (centerInfCommutator X).map (iotaPsi ψ) ∨
        (d * iotaPsi ψ β)⁻¹ * z ∈ (centerInfCommutator X).map (iotaPsi ψ) := by
  have hι := iotaPsi_injective ψ
  have hιc := iotaPsi_cV0 ψ hψ
  rintro _ ⟨z, hz, rfl⟩ hzc
  have hzc' : ∀ y ∈ X, z * y = y * z := fun y hy => hι (by
    rw [map_mul, map_mul]
    exact hzc _ (Subgroup.mem_map_of_mem _ hy))
  rcases hZ z hz hzc' with h | h | h | h
  · exact Or.inl (Subgroup.mem_map_of_mem _ h)
  · refine Or.inr (Or.inl ?_)
    rw [← map_inv_mul_gen _ hιc]
    exact Subgroup.mem_map_of_mem _ h
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [← map_inv_mul_gen'']
    exact Subgroup.mem_map_of_mem _ h
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [← map_mul_inv_mul_gen _ hιc]
    exact Subgroup.mem_map_of_mem _ h

include hψ in
theorem not_mem_map_of_not_mem_cV0 {U : Subgroup (vStab cv0)} (h : cV0 ∉ U) :
    d ∉ U.map (iotaPsi ψ) := by
  rintro ⟨y, hy, hyd⟩
  have hyc : y = cV0 := iotaPsi_injective ψ (hyd.trans (iotaPsi_cV0 ψ hψ).symm)
  exact h (hyc ▸ hy)

include hψ in
theorem not_mem_map_of_not_mem_inv_mul {U : Subgroup (vStab cv0)} {β : vStab cv0}
    (h : β⁻¹ * cV0 ∉ U) : (iotaPsi ψ β)⁻¹ * d ∉ U.map (iotaPsi ψ) := by
  rw [← map_inv_mul_gen' _ (iotaPsi_cV0 ψ hψ)]
  exact fun h' => h ((Subgroup.mem_map_iff_mem (iotaPsi_injective ψ)).1 h')

include hψ in
theorem hd_iotaPsi {U : Subgroup (vStab cv0)} {β : vStab cv0}
    (hd : ∀ u ∈ U, ∃ u' ∈ U, u' ≠ u ∧ IsConj (cV0 * β * u) (cV0 * β * u')) :
    ∀ u ∈ U.map (iotaPsi ψ), ∃ u' ∈ U.map (iotaPsi ψ), u' ≠ u ∧
      IsConj (d * iotaPsi ψ β * u) (d * iotaPsi ψ β * u') := by
  have hιc := iotaPsi_cV0 ψ hψ
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨u', hu', hne, hconj⟩ := hd u hu
  refine ⟨iotaPsi ψ u', Subgroup.mem_map_of_mem _ hu', fun h => hne (iotaPsi_injective ψ h), ?_⟩
  have h := (iotaPsi ψ).map_isConj hconj
  rwa [map_mul_mul_gen _ hιc β u, map_mul_mul_gen _ hιc β u'] at h

theorem he_iotaPsi {X : Subgroup (vStab cv0)} {β : vStab cv0} (hβ2 : β ^ 2 = 1)
    (hβK : β ∉ commutator (vStab cv0))
    (he : ∀ u ∈ commutator (vStab cv0), u * u = 1 → u ≠ 1 →
      2 * Nat.card X ∣ Nat.card (Subgroup.centralizer {u})) :
    ∀ u ∈ (commutator (vStab cv0)).map (iotaPsi ψ), IsConj (iotaPsi ψ β) u →
      2 * Nat.card (X.map (iotaPsi ψ)) ∣
        Nat.card (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {u} : Subgroup G) := by
  have hι := iotaPsi_injective ψ
  rintro _ ⟨u, hu, rfl⟩ hconj
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [map_one, isConj_one_left] at hconj
    exact hβK (by rw [hι (hconj.trans (map_one _).symm)]; exact Subgroup.one_mem _)
  rw [Subgroup.card_map_of_injective hι, inf_centralizer_iotaPsi, Subgroup.card_map_of_injective hι]
  exact he u hu (mul_self_of_isConj_gen hι hβ2 hconj) hu1

include hψ in
theorem hc_iotaPsi
    [Finite G] (T : Sylow 2 (vStab cv0)) {U : Subgroup (vStab cv0)}
    (hc : ∀ u ∈ U, u ≠ 1 → cV0 * u ∈ RA ∨ cV0 * u ∉ dH ψ) :
    ¬ 2 ∣ ((T : Subgroup (vStab cv0)).map (iotaPsi ψ)).index →
      ∀ u ∈ U.map (iotaPsi ψ), IsConj d (d * u) → u = 1 := by
  intro hTsyl
  rintro _ ⟨u, hu, rfl⟩ hconj
  by_contra hne
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hne (map_one _)
  have hmem : cV0 * u ∈ dH ψ := by
    rw [mem_dH_iff_iotaPsi, map_mul_gen _ (iotaPsi_cV0 ψ hψ)]
    exact hconj
  rcases hc u hu hu1 with h | h
  · exact not_mem_dH_of_mem_RA_of_sylow ψ hψ T hTsyl h hmem
  · exact h hmem

end Hyp

theorem mul_mul_self_gen {M : Type*} [Group M] {c u : M} (hc : ∀ y, c * y = y * c)
    (hc2 : c * c = 1) (hu : u * u = 1) : c * u * (c * u) = 1 := by
  rw [mul_assoc, ← mul_assoc u, ← hc u, mul_assoc, hu, mul_one, hc2]

theorem hc_of_rkH
    {G : Type*} [Group G] {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) {U : Subgroup (vStab cv0)}
    (h6 : ∀ u ∈ U, u ≠ 1 →
      cV0 * u ∈ RA ∨ (u * u = 1 ∧ rkH u = 2048 ∧ rkH (cV0 * u) ≠ 1860)) :
    ∀ u ∈ U, u ≠ 1 → cV0 * u ∈ RA ∨ cV0 * u ∉ dH ψ := by
  intro u hu hu1
  rcases h6 u hu hu1 with h | ⟨h2, hr, hr'⟩
  · exact Or.inl h
  · refine Or.inr (not_mem_dH_of_rkH_mul_2048 ψ hψ (mul_mul_self_gen commute_cV0 cV0_mul_self h2)
      ?_ hr')
    rw [cV0_mul_cV0_mul]
    exact hr

theorem two_dvd_index_centralizer_of_native
    {G : Type*} [Group G] [Finite G]
    (hG : ∀ L : Subgroup G, L.index ≠ 2) {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (T : Sylow 2 (vStab cv0))
    {β : vStab cv0} {X : Subgroup (vStab cv0)} (hβ2 : β ^ 2 = 1)
    (hβK : β ∉ commutator (vStab cv0)) (hXT : X ≤ T) (hcX : cV0 ∈ X) (hβX : β ∈ X)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hXsyl : Odd (X.relIndex (Subgroup.centralizer {β})))
    (hZ : ∀ z ∈ X, (∀ y ∈ X, z * y = y * z) → z ∈ centerInfCommutator X ∨
      cV0⁻¹ * z ∈ centerInfCommutator X ∨ β⁻¹ * z ∈ centerInfCommutator X ∨
      (cV0 * β)⁻¹ * z ∈ centerInfCommutator X)
    (hcU : cV0 ∉ centerInfCommutator X) (hβcU : β⁻¹ * cV0 ∉ centerInfCommutator X)
    (hd : ∀ u ∈ centerInfCommutator X, ∃ u' ∈ centerInfCommutator X, u' ≠ u ∧
      IsConj (cV0 * β * u) (cV0 * β * u'))
    (hc : ∀ u ∈ centerInfCommutator X, u ≠ 1 → cV0 * u ∈ RA ∨ cV0 * u ∉ dH ψ)
    (he : ∀ u ∈ commutator (vStab cv0), u * u = 1 → u ≠ 1 →
      2 * Nat.card X ∣ Nat.card (Subgroup.centralizer {u})) :
    2 ∣ (Subgroup.centralizer {d}).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hι := iotaPsi_injective ψ
  have hU : centerInfCommutator (X.map (iotaPsi ψ)) = (centerInfCommutator X).map (iotaPsi ψ) :=
    (map_centerInfCommutator hι X).symm
  have hTd := map_le_centralizer_iotaPsi ψ (T : Subgroup (vStab cv0))
  have hTodd : Odd (((T : Subgroup (vStab cv0)).map (iotaPsi ψ)).relIndex
      (Subgroup.centralizer {d})) := by
    rw [relIndex_centralizer_iotaPsi]
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 T.not_dvd_index)
  have hKT : ((commutator (vStab cv0)).map (iotaPsi ψ)).relIndex
      ((T : Subgroup (vStab cv0)).map (iotaPsi ψ)) = 2 :=
    NotTwoCentral.relIndex_eq_two_of_not_mem (H := Subgroup.centralizer {d})
      (by rw [relIndex_centralizer_iotaPsi, index_commutator_vStab_cv0]) hTd
      (Subgroup.mem_map_of_mem _ (hXT hβX)) (fun h => hβK ((Subgroup.mem_map_iff_mem hι).1 h))
  have hXsylG : Odd ((X.map (iotaPsi ψ)).relIndex
      (Subgroup.centralizer {d} ⊓ Subgroup.centralizer {iotaPsi ψ β})) := by
    rw [inf_centralizer_iotaPsi, Subgroup.relIndex_map_map_of_injective _ _ hι]
    exact hXsyl
  exact two_dvd_index_centralizer_of_extremal _ (T.isPGroup'.map _) hTd hTodd hKT
    (map_sq_eq_one_gen _ hβ2) (fun L hL => absurd hL (hG L)) ((T.isPGroup'.to_le hXT).map _)
    ⟨cV0, hcX, iotaPsi_cV0 ψ hψ⟩ (map_le_centralizer_iotaPsi ψ X) (map_le_centralizer_gen _ hXβ)
    hXsylG (U := (centerInfCommutator X).map (iotaPsi ψ))
    (fun x hx u hu => by
      rw [← hU] at hu ⊢
      exact NotTwoCentral.conj_mem_center_inf_commutator hx hu)
    (hZ_iotaPsi ψ hψ hZ) (not_mem_map_of_not_mem_cV0 ψ hψ hcU)
    (not_mem_map_of_not_mem_inv_mul ψ hψ hβcU) (hc_iotaPsi ψ hψ T hc) (hd_iotaPsi ψ hψ hd)
    (he_iotaPsi ψ hβ2 hβK he)

theorem two_dvd_index_centralizer_of_native_of_isSimpleGroup
    {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hG2 : Nat.card G ≠ 2) {d : G} (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (T : Sylow 2 (vStab cv0))
    {β : vStab cv0} {X : Subgroup (vStab cv0)} (hβ2 : β ^ 2 = 1)
    (hβK : β ∉ commutator (vStab cv0)) (hXT : X ≤ T) (hcX : cV0 ∈ X) (hβX : β ∈ X)
    (hXβ : X ≤ Subgroup.centralizer {β}) (hXsyl : Odd (X.relIndex (Subgroup.centralizer {β})))
    (hZ : ∀ z ∈ X, (∀ y ∈ X, z * y = y * z) → z ∈ centerInfCommutator X ∨
      cV0⁻¹ * z ∈ centerInfCommutator X ∨ β⁻¹ * z ∈ centerInfCommutator X ∨
      (cV0 * β)⁻¹ * z ∈ centerInfCommutator X)
    (hcU : cV0 ∉ centerInfCommutator X) (hβcU : β⁻¹ * cV0 ∉ centerInfCommutator X)
    (hd : ∀ u ∈ centerInfCommutator X, ∃ u' ∈ centerInfCommutator X, u' ≠ u ∧
      IsConj (cV0 * β * u) (cV0 * β * u'))
    (hc : ∀ u ∈ centerInfCommutator X, u ≠ 1 → cV0 * u ∈ RA ∨ cV0 * u ∉ dH ψ)
    (he : ∀ u ∈ commutator (vStab cv0), u * u = 1 → u ≠ 1 →
      2 * Nat.card X ∣ Nat.card (Subgroup.centralizer {u})) :
    2 ∣ (Subgroup.centralizer {d}).index :=
  two_dvd_index_centralizer_of_native (fun K hK => by
    have hN := Subgroup.normal_of_index_eq_two hK
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
    · rw [h, Subgroup.index_bot] at hK
      exact hG2 hK
    · rw [h, Subgroup.index_top] at hK
      exact absurd hK (by norm_num)) ψ hψ T hβ2 hβK hXT hcX hβX hXβ hXsyl hZ hcU hβcU hd hc he

end CFSG.Monster.B.GSide

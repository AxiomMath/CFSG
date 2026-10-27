module

public import CFSG.Walter.Ree.Thompson2.BaseRel.Iso
public import CFSG.Walter.Ree.Thompson3.Base

public section

namespace CFSG.Walter.Ree.T2

open CFSG.Walter.Ward CFSG.Walter.J1Recog Word BaseRel
open scoped Pointwise

section Thompson

variable {k : Type} [Field k] [CharP k 3] (σ : k ≃+* k) (d : k)

theorem two_ne_zero_of_charThree : (2 : k) ≠ 0 := by
  intro h
  have h3 := three_eq_zero' (k := k)
  exact one_ne_zero (by linear_combination h3 - h)

theorem thompsonJ_ne_one : ThompsonN.J σ ≠ 1 := by
  intro h
  have h1 : ((ThompsonN.J σ).κ : k) = ((1 : ThompsonN k σ).κ : k) := by rw [h]
  simp only [ThompsonN.J, ThompsonN.torus_κ, ThompsonN.one_κ, Units.val_neg, Units.val_one] at h1
  exact two_ne_zero_of_charThree (by linear_combination -h1)

theorem tY_ne_one : tY σ d ≠ 1 := by
  intro h
  have h1 := congrArg ThompsonN.α h
  simp [tY, pp] at h1

theorem thompsonJ_sq : ThompsonN.J σ ^ 2 = 1 := by
  rw [ThompsonN.J, ← map_pow, neg_one_sq, map_one]

theorem tT_pow_three : tT σ ^ 3 = 1 := by
  rw [pow_three', tT, pp, ThompsonN.mul_P, ThompsonN.mul_P]
  have h3 := three_eq_zero' (k := k)
  ext
  · rfl
  · simp
  · simp only [map_zero, mul_zero, sub_zero, add_zero, ThompsonN.one_β]
    linear_combination h3
  · simp

theorem tY_pow_nine : tY σ d ^ 9 = 1 := by
  rw [show 9 = 3 * 3 from rfl, pow_mul, tY_cube, pow_three', pp, ThompsonN.mul_P,
    ThompsonN.mul_P]
  have h3 := three_eq_zero' (k := k)
  ext
  · rfl
  · simp
  · simp
  · simp only [map_zero, mul_zero, sub_zero, add_zero, zero_pow two_ne_zero, ThompsonN.one_γ]
    linear_combination h3

theorem thompsonJ_conj_tT : (ThompsonN.J σ)⁻¹ * tT σ * ThompsonN.J σ = tT σ := by
  rw [tT, pp, ThompsonN.J_conj, neg_zero]

theorem thompsonJ_conj_tY : (ThompsonN.J σ)⁻¹ * tY σ d * ThompsonN.J σ = (tY σ d)⁻¹ := by
  rw [tY, pp, ThompsonN.J_conj, ThompsonN.inv_P]
  ext <;> simp

theorem tT_conj_tY : (tT σ)⁻¹ * tY σ d * tT σ = (tY σ d ^ 2)⁻¹ := by
  rw [mul_assoc, tY_mul_tT, tY_sq]
  simp only [tT, pp]
  rw [ThompsonN.inv_P, ThompsonN.inv_P, ThompsonN.mul_P]
  ext
  · rfl
  · simp
  · simp
  · simp only [map_zero, map_one, mul_zero, sub_zero, add_zero, mul_one, neg_zero,
      zero_pow two_ne_zero, one_pow]
    ring

theorem eq_one_of_sq_of_commute_tY (ν : ThompsonN k σ) (h2 : ν * ν = 1)
    (hc : ν * tY σ d = tY σ d * ν) : ν = 1 := by
  obtain ⟨κ, α, β, γ⟩ := ν
  have hκ : κ = 1 := by
    have h1 := congrArg ThompsonN.α hc
    simp only [ThompsonN.mul_α, tY, pp, Units.val_one] at h1
    exact Units.ext (by rw [Units.val_one]; linear_combination -h1)
  subst hκ
  have h2' := h2
  rw [ThompsonN.mul_P] at h2'
  have hα := congrArg ThompsonN.α h2'
  have hβ := congrArg ThompsonN.β h2'
  have hγ := congrArg ThompsonN.γ h2'
  simp only [ThompsonN.one_α, ThompsonN.one_β, ThompsonN.one_γ] at hα hβ hγ
  have h2k := two_ne_zero_of_charThree (k := k)
  have ha : α = 0 := (mul_eq_zero.mp (show 2 * α = 0 by linear_combination hα)).resolve_left h2k
  subst ha
  simp only [map_zero, mul_zero, zero_mul, sub_zero, add_zero, zero_pow two_ne_zero] at hβ hγ
  have hb : β = 0 := (mul_eq_zero.mp (show 2 * β = 0 by linear_combination hβ)).resolve_left h2k
  have hg : γ = 0 := (mul_eq_zero.mp (show 2 * γ = 0 by linear_combination hγ)).resolve_left h2k
  subst hb hg
  rfl

end Thompson

section Gens

variable {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k} {G : Type} [Group G]

theorem incl_injective {N : Subgroup G} (e : N ≃* ThompsonN k σ) : Function.Injective (incl e) :=
  fun _ _ h => e.symm.injective (Subtype.ext h)

theorem incl_mem {N : Subgroup G} (e : N ≃* ThompsonN k σ) (n : ThompsonN k σ) : incl e n ∈ N :=
  (e.symm n).2

@[expose] noncomputable def baseGens {N : Subgroup G} (e : N ≃* ThompsonN k σ) (K : G) (d : k) :
    Fin 4 → G :=
  ![incl e (ThompsonN.J σ), K, incl e (tT σ), incl e (tY σ d)]

variable {N : Subgroup G} (e : N ≃* ThompsonN k σ) (K : G) (d : k)

theorem baseGens_zero : baseGens e K d 0 = incl e (ThompsonN.J σ) := rfl

theorem baseGens_one : baseGens e K d 1 = K := rfl

theorem baseGens_two : baseGens e K d 2 = incl e (tT σ) := rfl

theorem baseGens_three : baseGens e K d 3 = incl e (tY σ d) := rfl

theorem baseGens_rels3024 (hK2 : K * K = 1)
    (hKinv : ∀ t : kˣ, K⁻¹ * incl e (ThompsonN.torus σ t) * K = incl e (ThompsonN.torus σ t⁻¹))
    (hrel : K * incl e (pp σ 0 (-1) 1) * K * (incl e (pp σ 0 (-1) 1))⁻¹ * K =
      incl e (tY σ d) ^ 2 * incl e (ThompsonN.J σ)) :
    ∀ w ∈ rels3024, ev (baseGens e K d) w = 1 := by
  intro w hw
  simp only [rels3024, nRels, kRels, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hw
  rcases hw with ((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | rfl
  all_goals simp only [ev_pow, ev_append, ev_gen, ev_inv, ev_comm, BaseRel.wj, BaseRel.wk,
    BaseRel.wt, BaseRel.wy, relA, baseGens_zero, baseGens_one, baseGens_two, baseGens_three]
  · rw [← map_pow, thompsonJ_sq, map_one]
  · rw [← map_pow, tT_pow_three, map_one]
  · rw [← map_pow, tY_pow_nine, map_one]
  · have h := congrArg (incl e) (thompsonJ_conj_tT σ)
    rw [map_mul, map_mul, map_inv] at h
    calc (incl e (ThompsonN.J σ))⁻¹ * (incl e (tT σ))⁻¹ * incl e (ThompsonN.J σ) * incl e (tT σ)
        = ((incl e (ThompsonN.J σ))⁻¹ * incl e (tT σ) * incl e (ThompsonN.J σ))⁻¹ *
          incl e (tT σ) := by group
      _ = 1 := by rw [h, inv_mul_cancel]
  · have h := congrArg (incl e) (thompsonJ_conj_tY σ d)
    have hJ := congrArg (incl e) (thompsonJ_sq σ)
    rw [map_mul, map_mul, map_inv, map_inv] at h
    rw [map_pow, map_one] at hJ
    have hJi : (incl e (ThompsonN.J σ))⁻¹ = incl e (ThompsonN.J σ) :=
      inv_eq_of_mul_eq_one_right (by rw [← sq, hJ])
    rw [hJi] at h
    calc incl e (ThompsonN.J σ) * incl e (tY σ d) * incl e (ThompsonN.J σ) * incl e (tY σ d)
        = (incl e (ThompsonN.J σ) * incl e (tY σ d) * incl e (ThompsonN.J σ)) *
          incl e (tY σ d) := rfl
      _ = 1 := by rw [h, inv_mul_cancel]
  · have h := congrArg (incl e) (tT_conj_tY σ d)
    rw [map_mul, map_mul, map_inv, map_inv, map_pow] at h
    calc (incl e (tT σ))⁻¹ * incl e (tY σ d) * incl e (tT σ) * incl e (tY σ d) ^ 2
        = ((incl e (tT σ))⁻¹ * incl e (tY σ d) * incl e (tT σ)) * incl e (tY σ d) ^ 2 := rfl
      _ = 1 := by rw [h, inv_mul_cancel]
  · rw [sq, hK2]
  · have h := hKinv (-1)
    rw [inv_neg_one] at h
    change K⁻¹ * incl e (ThompsonN.J σ) * K = incl e (ThompsonN.J σ) at h
    calc (incl e (ThompsonN.J σ))⁻¹ * K⁻¹ * incl e (ThompsonN.J σ) * K
        = (incl e (ThompsonN.J σ))⁻¹ * (K⁻¹ * incl e (ThompsonN.J σ) * K) := by group
      _ = 1 := by rw [h, inv_mul_cancel]
  · have hP0 : incl e (pp σ 0 (-1) 1) = (incl e (tT σ))⁻¹ * incl e (tY σ d) ^ 3 := by
      rw [← tT_inv_mul_tY_cube σ d, map_mul, map_inv, map_pow]
    rw [hP0] at hrel
    calc K * (incl e (tT σ))⁻¹ * incl e (tY σ d) ^ 3 * K * (incl e (tY σ d))⁻¹ ^ 3 *
          incl e (tT σ) * K * (incl e (ThompsonN.J σ))⁻¹ * (incl e (tY σ d))⁻¹ ^ 2
        = (K * ((incl e (tT σ))⁻¹ * incl e (tY σ d) ^ 3) * K *
            ((incl e (tT σ))⁻¹ * incl e (tY σ d) ^ 3)⁻¹ * K) *
          (incl e (tY σ d) ^ 2 * incl e (ThompsonN.J σ))⁻¹ := by group
      _ = 1 := by rw [hrel, mul_inv_cancel]

end Gens

section Centralizer

variable {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k} {G : Type} [Group G] [Finite G]

theorem eq_one_of_commute_tY
    (h : ReeTypeHyp G) (P : Sylow 3 G)
    (e : Subgroup.normalizer ((P : Subgroup G) : Set G) ≃* ThompsonN k σ) (d : k) {Z : G}
    (hZ2 : Z * Z = 1) (hZY : Z * incl e (tY σ d) = incl e (tY σ d) * Z) : Z = 1 := by
  set Y := incl e (tY σ d) with hYdef
  have hYN : Y ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := incl_mem e _
  have hQ : IsPGroup 3 (Subgroup.zpowers Y) := by
    have hY9 : Y ^ 9 = 1 := by rw [hYdef, ← map_pow, tY_pow_nine, map_one]
    have hdvd : orderOf Y ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by norm_num [hY9])
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hYP : Y ∈ (P : Subgroup G) := by
    have h1 : Y ∈ Subgroup.zpowers Y ⊓ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
      ⟨Subgroup.mem_zpowers Y, hYN⟩
    have h2 : Y ∈ Subgroup.zpowers Y ⊓ (P : Subgroup G) := by
      rw [← hQ.inf_normalizer_sylow P]
      exact h1
    exact h2.2
  have hY1 : Y ≠ 1 := fun h1 => tY_ne_one σ d (incl_injective e (h1.trans (map_one _).symm))
  have hZinv : Z⁻¹ = Z := inv_eq_of_mul_eq_one_right hZ2
  have hmem : Y ∈ (P : Subgroup G) ⊓ (MulAut.conj Z • (P : Subgroup G)) := by
    refine Subgroup.mem_inf.mpr ⟨hYP, ?_⟩
    rw [WardLocal.mem_conj_smul_iff, hZinv, hZY, mul_assoc, hZ2, mul_one]
    exact hYP
  have heq : (P : Subgroup G) = MulAut.conj Z • (P : Subgroup G) := by
    rcases (WardLocal.ward_two_three h P).2.1 Z with h0 | h0
    · rw [h0] at hmem
      exact absurd ((Subgroup.mem_bot).mp hmem) hY1
    · exact Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp h0) (by rw [WardLocal.card_conj_smul])
  have hZN : Z ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : x ∈ (P : Subgroup G) ↔ Z * x * Z ∈ (P : Subgroup G) := by
      conv_lhs => rw [heq]
      rw [WardLocal.mem_conj_smul_iff, hZinv]
    rw [hZinv]
    exact key
  have hZν : incl e (e ⟨Z, hZN⟩) = Z := by simp [incl]
  have hν2 : e ⟨Z, hZN⟩ * e ⟨Z, hZN⟩ = 1 :=
    incl_injective e (by rw [map_mul, hZν, hZ2, map_one])
  have hνY : e ⟨Z, hZN⟩ * tY σ d = tY σ d * e ⟨Z, hZN⟩ :=
    incl_injective e (by rw [map_mul, map_mul, hZν]; exact hZY)
  rw [← hZν, eq_one_of_sq_of_commute_tY σ d _ hν2 hνY, map_one]

theorem baseGens_kt3
    (h : ReeTypeHyp G) (P : Sylow 3 G)
    (e : Subgroup.normalizer ((P : Subgroup G) : Set G) ≃* ThompsonN k σ) (K : G) (d : k)
    (hf : ∀ w ∈ rels3024, ev (baseGens e K d) w = 1) : ev (baseGens e K d) kt3 = 1 := by
  have hsq := ev_kt3_sq _ hf
  have hcomm := ev_kt3_comm _ hf
  rw [ev_append] at hsq
  simp only [ev_append, BaseRel.wy, ev_gen, baseGens_three] at hcomm
  exact eq_one_of_commute_tY h P e d hsq hcomm

end Centralizer

section Base

variable {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k} {G : Type} [Group G]
variable {N : Subgroup G} {e : N ≃* ThompsonN k σ} {K : G} {d : k}

theorem baseGens_rels1512 (hf : ∀ w ∈ rels3024, ev (baseGens e K d) w = 1)
    (hkt : ev (baseGens e K d) kt3 = 1) : ∀ w ∈ rels1512, ev (baseGens e K d) w = 1 := by
  intro w hw
  have hw' : w ∈ rels3024 ∨ w = kt3 := by
    simp only [rels3024, rels1512, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hw ⊢
    tauto
  rcases hw' with hw' | rfl
  · exact hf w hw'
  · exact hkt

noncomputable def baseHom (hf : ∀ w ∈ rels1512, ev (baseGens e K d) w = 1) : PGammaL28 →* G :=
  (lift rels1512 (baseGens e K d) hf).comp iso1512.symm.toMonoidHom

variable (hf : ∀ w ∈ rels1512, ev (baseGens e K d) w = 1)

theorem baseHom_j : baseHom hf PGammaL28.j = incl e (ThompsonN.J σ) := by
  simp only [baseHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, iso1512_symm_j, lift_of,
    baseGens_zero]

theorem baseHom_k : baseHom hf PGammaL28.k = K := by
  simp only [baseHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, iso1512_symm_k, lift_of,
    baseGens_one]

theorem baseHom_t : baseHom hf PGammaL28.t = incl e (tT σ) := by
  simp only [baseHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, iso1512_symm_t, lift_of,
    baseGens_two]

theorem baseHom_y : baseHom hf PGammaL28.y = incl e (tY σ d) := by
  simp only [baseHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, iso1512_symm_y, lift_of,
    baseGens_three]

theorem baseHom_injective : Function.Injective (baseHom hf) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  by_contra ha1
  have hj := j_mem_of_normal (MonoidHom.normal_ker (baseHom hf)) (MonoidHom.mem_ker.mpr ha) ha1
  rw [MonoidHom.mem_ker, baseHom_j] at hj
  exact thompsonJ_ne_one σ (incl_injective e (hj.trans (map_one _).symm))

end Base

theorem rType_of_relA
    {k : Type} [Field k] [Fintype k] [CharP k 3] {σ : k ≃+* k} {G : Type}
    [Group G] [Finite G] (h : ReeTypeHyp G) (P : Sylow 3 G)
    (e : Subgroup.normalizer ((P : Subgroup G) : Set G) ≃* ThompsonN k σ) (K : G)
    (hKN : K ∉ Subgroup.normalizer ((P : Subgroup G) : Set G)) (hK2 : K * K = 1)
    (hKinv : ∀ t : kˣ, K⁻¹ * incl e (ThompsonN.torus σ t) * K = incl e (ThompsonN.torus σ t⁻¹))
    (d : k) (hrel : K * incl e (pp σ 0 (-1) 1) * K * (incl e (pp σ 0 (-1) 1))⁻¹ * K =
      incl e (tY σ d) ^ 2 * incl e (ThompsonN.J σ)) :
    Nonempty (RType G k σ d) := by
  have hf3 := baseGens_rels3024 e K d hK2 hKinv hrel
  have hf := baseGens_rels1512 hf3 (baseGens_kt3 h P e K d hf3)
  exact ⟨⟨h, P, e, K, hKN, hKinv, baseHom hf, baseHom_injective hf, baseHom_j hf, baseHom_k hf,
    baseHom_t hf, baseHom_y hf⟩⟩

theorem rType_of_K_P0_K
    {k : Type} [Field k] [Fintype k] [CharP k 3] {σ : k ≃+* k} {G : Type}
    [Group G] [Finite G] (h : ReeTypeHyp G) (P : Sylow 3 G)
    (e : Subgroup.normalizer ((P : Subgroup G) : Set G) ≃* ThompsonN k σ) (K : G)
    (hKN : K ∉ Subgroup.normalizer ((P : Subgroup G) : Set G)) (hK2 : K * K = 1)
    (hKinv : ∀ t : kˣ, K⁻¹ * incl e (ThompsonN.torus σ t) * K = incl e (ThompsonN.torus σ t⁻¹))
    (d : k) (hrel : K * incl e (pp σ 0 (-1) 1) * K =
      incl e (tY σ d ^ 2) * incl e (ThompsonN.J σ) * K * incl e (pp σ 0 (-1) 1)) :
    Nonempty (RType G k σ d) := by
  refine rType_of_relA h P e K hKN hK2 hKinv d ?_
  rw [hrel, ← map_pow]
  calc incl e (tY σ d ^ 2) * incl e (ThompsonN.J σ) * K * incl e (pp σ 0 (-1) 1) *
        (incl e (pp σ 0 (-1) 1))⁻¹ * K
      = incl e (tY σ d ^ 2) * incl e (ThompsonN.J σ) * (K * K) := by group
    _ = incl e (tY σ d ^ 2) * incl e (ThompsonN.J σ) := by rw [hK2, mul_one]

theorem baseExists_of_relA
    (H : ∀ (k : Type) [Field k] [Fintype k] [CharP k 3] (G : Type) [Group G] [Finite G]
      (_h : ReeTypeHyp G) (σ : k ≃+* k), (∃ P : Sylow 3 G,
        Nonempty (Subgroup.normalizer ((P : Subgroup G) : Set G) ≃* ThompsonN k σ)) →
      ∃ (P : Sylow 3 G) (e : Subgroup.normalizer ((P : Subgroup G) : Set G) ≃* ThompsonN k σ)
        (K : G) (d : k), K ∉ Subgroup.normalizer ((P : Subgroup G) : Set G) ∧ K * K = 1 ∧
        (∀ t : kˣ, K⁻¹ * incl e (ThompsonN.torus σ t) * K = incl e (ThompsonN.torus σ t⁻¹)) ∧
        K * incl e (pp σ 0 (-1) 1) * K * (incl e (pp σ 0 (-1) 1))⁻¹ * K =
          incl e (tY σ d) ^ 2 * incl e (ThompsonN.J σ)) :
    BaseExists := by
  intro k _ _ _ G _ _ h σ hP
  obtain ⟨P, e, K, d, hKN, hK2, hKinv, hrel⟩ := H k G h σ hP
  exact ⟨d, rType_of_relA h P e K hKN hK2 hKinv d hrel⟩

end CFSG.Walter.Ree.T2

module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26D12Shape
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA2

public section

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure ConfR (δ μ : Geo H M) (U : Subgroup G) : Prop where
  b : 1 < bMin H M
  sig : SitSigma δ μ U
  hQ : Qv μ ≤ U
  hR : ¬ pCoreOf 2 U ≤ Qv δ
  hQδ : Qv δ ≤ Qv μ

structure SFourC (U T C : Subgroup G) : Prop where
  le_T : T ≤ U
  le_C : C ≤ U
  sup : T ⊔ C = U
  inf : T ⊓ C = ⊥
  comm : ∀ t ∈ T, ∀ c ∈ C, t * c = c * t
  perm : Nonempty (↥T ≃* Perm (Fin 4))
  pgrp : IsPGroup 2 C

theorem eq_one_of_mem_pCore_perm3 {X : Type*} [Group X] [Finite X] (T : Subgroup X)
    (eT : ↥T ≃* Perm (Fin 3)) {z : X} (hzT : z ∈ T) (hz : z ∈ CFSG.Open.pCore 2 X) : z = 1 := by
  by_contra hz1
  have hne : eT ⟨z, hzT⟩ ≠ 1 := fun h => hz1 (by simpa using congrArg Subtype.val (eT.injective (h.trans (map_one eT).symm)))
  obtain ⟨g, hg⟩ := exists_not_sq_perm3 _ hne
  set gt : ↥T := eT.symm g with hgt
  have hnorm : (CFSG.Open.pCore 2 X).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hy : z * ((gt : X) * z * (gt : X)⁻¹) ∈ CFSG.Open.pCore 2 X :=
    Subgroup.mul_mem _ hz (hnorm.conj_mem z hz _)
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := X) ⟨_, hy⟩
  have hk' : (z * ((gt : X) * z * (gt : X)⁻¹)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hk'' : (eT ⟨z, hzT⟩ * (g * eT ⟨z, hzT⟩ * g⁻¹)) ^ 2 ^ k = 1 := by
    have : (⟨z, hzT⟩ * (gt * ⟨z, hzT⟩ * gt⁻¹) : ↥T) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    have := congrArg eT this
    simpa [hgt] using this
  exact hg (sq_of_two_pow_perm3 hk'')

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

omit [Finite G] in
theorem inf_eq (h : ConfR δ μ U) : Qv μ ⊓ U = Qv μ := inf_eq_left.mpr h.hQ

omit [Finite G] in
theorem normal_P (h : ConfR δ μ U) :
    stab μ ≤ Subgroup.normalizer ((Qv μ ⊓ U : Subgroup G) : Set G) := by
  rw [h.inf_eq]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab μ)

theorem vtype_delta (hA : F53Amalgam H M S) (h : ConfR δ μ U) : vtype δ = false :=
  (h.sig.counts hA h.normal_P h.hR).1

theorem vtype_mu (hA : F53Amalgam H M S) (h : ConfR δ μ U) : vtype μ = true := by
  have h1 := vtype_delta hA h
  have h2 := vtype_ne_of_adj h.sig.adj
  rw [h1] at h2
  cases hv : vtype μ
  · exact absurd hv.symm h2
  · rfl

omit [Finite G] in
theorem card_pCoreOf (X : Subgroup G) :
    Nat.card (pCoreOf 2 X) = Nat.card (CFSG.Open.pCore 2 ↥X) :=
  Subgroup.card_map_of_injective (Subgroup.subtype_injective X)

theorem card_U (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    Nat.card U = 3 * Nat.card (Qv μ) := by
  obtain ⟨e⟩ := h.sig.shape_three_of_not_le hA h.normal_P h.hR
  obtain ⟨-, h2, -, -⟩ := h.sig.counts hA h.normal_P h.hR
  have h1 : Nat.card ↥U = Nat.card (OTwoQuot U) * Nat.card (CFSG.Open.pCore 2 ↥U) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h6 : Nat.card (OTwoQuot U) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  have h3 : (pCoreOf 2 U).relIndex (Qv μ ⊓ U) * Nat.card (pCoreOf 2 U) =
      Nat.card (Qv μ ⊓ U : Subgroup G) := by
    have := Subgroup.relIndex_mul_card (pCoreOf 2 U) (Qv μ ⊓ U)
    rwa [inf_of_le_left (h.sig.R_le_P)] at this
  rw [h2, card_pCoreOf, h.inf_eq] at h3
  rw [h1, h6]
  omega

theorem eq_bot_of_char (hA : F53Amalgam H M S) (h : ConfR δ μ U)
    (K : Subgroup ↥(Qv μ)) [K.Characteristic]
    (hK : U ≤ Subgroup.normalizer ((K.map (Qv μ).subtype : Subgroup G) : Set G)) : K = ⊥ := by
  have hμC : stab μ ≤ Subgroup.normalizer ((K.map (Qv μ).subtype : Subgroup G) : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab μ)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic K)
  have hδC : stab δ ≤ Subgroup.normalizer ((K.map (Qv μ).subtype : Subgroup G) : Set G) := by
    rw [← h.sig.gen]; exact sup_le hK (inf_le_right.trans hμC)
  have hle : (K.map (Qv μ).subtype : Subgroup G) ≤ stab δ ⊓ stab μ :=
    (Subgroup.map_subtype_le K).trans (h.inf_eq ▸ h.sig.P_le_edge hA)
  have := eq_bot_of_normalizes_both hA h.sig.adj hle hδC hμC
  exact (Subgroup.map_eq_bot_iff_of_injective K (Subgroup.subtype_injective _)).mp this

omit [Finite G] in
theorem characteristic_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) (K : Subgroup A)
    [hK : K.Characteristic] : (K.map e.toMonoidHom).Characteristic := by
  refine ⟨fun φ => ?_⟩
  ext x
  have h := hK.fixed (e.trans (φ.trans e.symm))
  have hx : x ∈ Subgroup.comap φ.toMonoidHom (K.map e.toMonoidHom) ↔
      e.symm (φ x) ∈ K := by
    simp only [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, hkx⟩
      have : e.symm (φ x) = k := by rw [← show e k = φ x from hkx]; simp
      rwa [this]
    · intro hk
      exact ⟨_, hk, by simp⟩
  rw [hx, Subgroup.mem_map]
  have h2 : e.symm x ∈ Subgroup.comap (e.trans (φ.trans e.symm)).toMonoidHom K ↔ e.symm x ∈ K := by
    rw [h]
  simp only [Subgroup.mem_comap] at h2
  simp at h2
  constructor
  · intro hk
    exact ⟨e.symm x, h2.mp (by simpa using hk), by simp⟩
  · rintro ⟨k, hk, rfl⟩
    simpa using h2.mpr (by simpa using hk)

theorem pushing_up (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    ∃ T C : Subgroup G, SFourC U T C := by
  obtain ⟨e⟩ := h.sig.shape_three_of_not_le hA h.normal_P h.hR
  have hP2 : IsPGroup 2 (Qv μ) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (stab μ)
  set Sg : Subgroup ↥U := (Qv μ).subgroupOf U with hSg
  let e₁ : ↥Sg ≃* ↥(Qv μ) := Subgroup.subgroupOfEquivOfLe h.hQ
  have hcard : Nat.card ↥U = 3 * Nat.card ↥Sg := by
    rw [h.card_U hA]; congr 1; exact (Nat.card_congr e₁.toEquiv).symm
  have hno : ∀ K : Subgroup ↥U, K ≤ Sg → (K.subgroupOf Sg).Characteristic → K.Normal → K = ⊥ := by
    intro K hKS hKc hKn
    have := hKc
    have hK' : ((K.subgroupOf Sg).map e₁.toMonoidHom).Characteristic :=
      characteristic_map e₁ (K.subgroupOf Sg)
    have hmem : ∀ y : G, y ∈ (((K.subgroupOf Sg).map e₁.toMonoidHom).map (Qv μ).subtype :
        Subgroup G) ↔ ∃ k ∈ K, ((k : ↥U) : G) = y := by
      intro y
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a.1, ha, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        refine ⟨_, ⟨⟨k, hKS hk⟩, hk, rfl⟩, rfl⟩
    have hU : U ≤ Subgroup.normalizer
        ((((K.subgroupOf Sg).map e₁.toMonoidHom).map (Qv μ).subtype : Subgroup G) : Set G) := by
      intro u hu
      rw [Subgroup.mem_normalizer_iff]
      have key : ∀ u ∈ U, ∀ x : G,
          x ∈ (((K.subgroupOf Sg).map e₁.toMonoidHom).map (Qv μ).subtype : Subgroup G) →
          u * x * u⁻¹ ∈ (((K.subgroupOf Sg).map e₁.toMonoidHom).map (Qv μ).subtype : Subgroup G) := by
        intro u hu x hx
        obtain ⟨k, hk, rfl⟩ := (hmem x).mp hx
        refine (hmem _).mpr ⟨⟨u, hu⟩ * k * ⟨u, hu⟩⁻¹, hKn.conj_mem k hk _, rfl⟩
      intro x
      refine ⟨key u hu x, fun hx => ?_⟩
      have := key u⁻¹ (U.inv_mem hu) _ hx
      simpa [mul_assoc] using this
    have hbot := eq_bot_of_char hA h _ hU
    rw [eq_bot_iff]
    intro k hk
    have : (⟨k, hKS hk⟩ : ↥Sg) ∈ K.subgroupOf Sg := hk
    have h2 := Subgroup.mem_map_of_mem e₁.toMonoidHom this
    rw [hbot, Subgroup.mem_bot] at h2
    have h3 : (⟨k, hKS hk⟩ : ↥Sg) = 1 := e₁.injective (by simpa using h2)
    exact Subgroup.mem_bot.mpr (by simpa using congrArg (fun z : ↥Sg => ((z : ↥U) : G)) h3)
  have key := Fan86.sigma3PushingUp ↥U Sg ⟨e⟩ (hP2.comap_subtype) hcard hno
  rcases key with ⟨T, E, ⟨eT⟩, -, hcomm, hTE, hsup⟩ | ⟨T, C, ⟨eT⟩, hC, hcomm, hTC, hsup⟩
  · exfalso
    set t₃ : ↥U := ((eT.symm (swap 0 1 * swap 1 2) : ↥T) : ↥U) with ht₃
    have ht₃T : t₃ ∈ T := (eT.symm (swap 0 1 * swap 1 2)).2
    have hcen : ∀ ρ ∈ CFSG.Open.pCore 2 ↥U, t₃ * ρ = ρ * t₃ := by
      intro ρ hρ
      obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute hcomm (hsup ▸ Subgroup.mem_top ρ)
      have hz : t₃ * a * t₃⁻¹ * a⁻¹ = 1 := by
        refine eq_one_of_mem_pCore_perm3 T eT (z := t₃ * a * t₃⁻¹ * a⁻¹)
          (T.mul_mem (T.mul_mem (T.mul_mem ht₃T ha) (T.inv_mem ht₃T)) (T.inv_mem ha)) ?_
        have hnorm : (CFSG.Open.pCore 2 ↥U).Normal := CFSG.LieType.BorelTits.pCore_normal 2
        have h1 : t₃ * ρ * t₃⁻¹ * ρ⁻¹ = t₃ * a * t₃⁻¹ * a⁻¹ := by
          have e1 := hcomm t₃ ht₃T b hb
          have e2 := hcomm a ha b hb
          subst hab
          calc t₃ * (a * b) * t₃⁻¹ * (a * b)⁻¹ = t₃ * a * (b * t₃⁻¹) * b⁻¹ * a⁻¹ := by group
            _ = t₃ * a * t₃⁻¹ * a⁻¹ := by
              have : b * t₃⁻¹ = t₃⁻¹ * b := by
                rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← e1]; group
              rw [this]; group
        rw [← h1]
        exact Subgroup.mul_mem _ (hnorm.conj_mem ρ hρ t₃) (Subgroup.inv_mem _ hρ)
      have : t₃ * a = a * t₃ := by
        have := congrArg (· * (a * t₃)) hz
        simp only [one_mul] at this
        rw [← this]; group
      subst hab
      calc t₃ * (a * b) = (t₃ * a) * b := by group
        _ = a * (t₃ * b) := by rw [this]; group
        _ = a * (b * t₃) := by rw [hcomm t₃ ht₃T b hb]
        _ = a * b * t₃ := by group
    have hmem : (t₃ : ↥U) ∈ CFSG.Open.pCore 2 ↥U := by
      have hx : ((t₃ : ↥U) : G) ∈ U ⊓ Subgroup.centralizer (pCoreOf 2 U : Set G) := by
        refine ⟨t₃.2, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
        obtain ⟨ρ, hρ, rfl⟩ := hr
        exact (congrArg Subtype.val (hcen ρ hρ)).symm
      obtain ⟨ρ, hρ, hρe⟩ := h.sig.centralizer_le_R hA hx
      exact (Subtype.ext hρe) ▸ hρ
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥U) ⟨t₃, hmem⟩
    have h1 : t₃ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (eT.symm (swap 0 1 * swap 1 2) : ↥T) ^ 2 ^ k = 1 := Subtype.ext h1
    have h3 := congrArg eT h2
    rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h3
    have h4 := sq_of_two_pow_perm3 h3
    revert h4
    decide +kernel
  · refine ⟨T.map U.subtype, C.map U.subtype, ⟨Subgroup.map_subtype_le T,
      Subgroup.map_subtype_le C, ?_, ?_, ?_, ?_, hC.map _⟩⟩
    · rw [← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    · rw [← Subgroup.map_inf T C U.subtype (Subgroup.subtype_injective U), hTC, Subgroup.map_bot]
    · rintro _ ⟨t, ht, rfl⟩ _ ⟨c, hc, rfl⟩
      exact congrArg Subtype.val (hcomm t ht c hc)
    · exact ⟨(T.equivMapOfInjective U.subtype (Subgroup.subtype_injective U)).symm.trans eT⟩

end ConfR

end CFSG.Quasithin.F53

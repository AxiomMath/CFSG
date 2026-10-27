module

public import CFSG.LocalAnalysis.SteinbergBNGMSNormalRootData
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXStrictRankStrongClosure
public import CFSG.LocalAnalysis.SteinbergBTSingerAdjoinField
public import CFSG.Quasithin.SteinbergOuterPrimeControl

public section

namespace CFSG.LocalAnalysis.SteinbergBT

open Subgroup CFSG CFSG.LocalAnalysis
open scoped IsMulCommutative Pointwise

universe u

section Linear

variable {A : Type*} [Group A] [IsElementaryAbelian 2 A]

@[expose] noncomputable def linAut : MulAut A →* (Additive A ≃ₗ[ZMod 2] Additive A) where
  toFun α := (MulEquiv.toAdditive α).toLinearEquiv fun c x =>
    ZMod.map_smul (MulEquiv.toAdditive α).toAddMonoidHom c x
  map_one' := by
    ext x
    rfl
  map_mul' α β := by
    ext x
    rfl

theorem linAut_apply (α : MulAut A) (x : A) :
    linAut α (Additive.ofMul x) = Additive.ofMul (α x) := rfl

theorem linAut_pow_apply (α : MulAut A) (j : ℕ) (w : Additive A) :
    (((linAut α : Additive A ≃ₗ[ZMod 2] Additive A) : Module.End (ZMod 2) (Additive A)) ^ j) w =
      linAut (α ^ j) w := by
  induction j generalizing w with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, map_mul]
    rfl

theorem linAut_symm (α : MulAut A) : (linAut α).symm = linAut α⁻¹ := by
  rw [map_inv]
  rfl

end Linear

section FieldFacts

theorem card_fixed_sq_le_card {F K : Type*} [Field F] [Field K] [Algebra F K] [Finite K]
    {σ : K ≃ₐ[F] K} (hσ : σ ≠ 1) : Nat.card {k : K // σ k = k} ^ 2 ≤ Nat.card K := by
  classical
  have : Finite F := Finite.of_injective _ (algebraMap F K).injective
  have : FiniteDimensional F K := Module.Finite.of_finite
  have : Finite (K ≃ₐ[F] K) :=
    Finite.of_injective (fun f : K ≃ₐ[F] K => (f : K → K)) DFunLike.coe_injective
  set H := zpowers σ with hH
  set E := IntermediateField.fixedField H with hE
  have hrank : Module.finrank E K = Nat.card H := IntermediateField.finrank_fixedField_eq_card H
  have hH2 : 2 ≤ Nat.card H := by
    rw [hH, Nat.card_zpowers]
    have h1 : orderOf σ ≠ 1 := fun h => hσ (orderOf_eq_one_iff.1 h)
    have h0 : 0 < orderOf σ := orderOf_pos σ
    omega
  have hfix : Nat.card {k : K // σ k = k} = Nat.card E := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun k => ?_)
    rw [hE, IntermediateField.mem_fixedField_iff]
    constructor
    · intro hk f hf
      have hle : H ≤ MulAction.stabilizer (K ≃ₐ[F] K) k :=
        zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hk)
      exact MulAction.mem_stabilizer_iff.1 (hle hf)
    · intro hk
      exact hk σ (mem_zpowers σ)
  have : Fintype K := Fintype.ofFinite K
  have : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card K = Fintype.card E ^ Module.finrank E K := Module.card_eq_pow_finrank
  rw [hfix, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcard]
  exact Nat.pow_le_pow_right Fintype.card_pos (hrank ▸ hH2)

theorem isCyclic_quotient_of_ker_eq {P : Type*} [Group P] {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {n : ℕ} (hK : Fintype.card K = 2 ^ n) (φ : P →* (K ≃ₐ[ZMod 2] K))
    {N : Subgroup P} [N.Normal] (hker : φ.ker = N) :
    IsCyclic (P ⧸ N) ∧ Nat.card (P ⧸ N) ∣ n := by
  have e : P ⧸ N ≃* φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  have hGal : Nat.card (K ≃ₐ[ZMod 2] K) = n := by
    rw [IsGalois.card_aut_eq_finrank]
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [ZMod.card, hK] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  refine ⟨isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective, ?_⟩
  rw [Nat.card_congr e.toEquiv, ← hGal]
  exact Subgroup.card_subgroup_dvd_card φ.range

theorem pRank_two_le_one_of_isCyclic {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] :
    CFSG.pRank 2 Q ≤ 1 :=
  CFSG.Quasithin.OuterPrimeControl.pRank_le_one_of_forall_isCyclic fun _ _ => inferInstance

end FieldFacts

section Groups

variable {D : Type u} [Group D]

theorem exists_mul_eq_of_mem_sup {U R : Subgroup D} (hRU : R ≤ centralizer (U : Set D)) {v : D}
    (hv : v ∈ U ⊔ R) : ∃ u ∈ U, ∃ r ∈ R, u * r = v := by
  have hcoe := coe_mul_of_right_le_normalizer_left U R (hRU.trans (centralizer_le_normalizer _))
  have hv' : v ∈ (U : Set D) * (R : Set D) := by
    rw [← hcoe]
    exact hv
  obtain ⟨u, hu, r, hr, huv⟩ := Set.mem_mul.1 hv'
  exact ⟨u, hu, r, hr, huv⟩

theorem isElementaryAbelian_sup_of_centralizes {p : ℕ} {U R : Subgroup D}
    (hU : IsElementaryAbelian p U) (hR : IsElementaryAbelian p R)
    (hRU : R ≤ centralizer (U : Set D)) : IsElementaryAbelian p ↥(U ⊔ R) := by
  have hUc : ∀ a ∈ U, ∀ b ∈ U, Commute a b := fun a ha b hb =>
    congrArg Subtype.val (hU.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hRc : ∀ a ∈ R, ∀ b ∈ R, Commute a b := fun a ha b hb =>
    congrArg Subtype.val (hR.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUR : ∀ a ∈ U, ∀ b ∈ R, Commute a b := fun a ha b hb => mem_centralizer_iff.1 (hRU hb) a ha
  have hUp : ∀ a ∈ U, a ^ p = 1 := fun a ha => by
    have := hU
    exact elemPow_eq_one_of_isElementaryAbelian a ha
  have hRp : ∀ a ∈ R, a ^ p = 1 := fun a ha => by
    have := hR
    exact elemPow_eq_one_of_isElementaryAbelian a ha
  exact
    { is_comm := ⟨fun x y => by
        obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_eq_of_mem_sup hRU x.2
        obtain ⟨a', ha', b', hb', hy⟩ := exists_mul_eq_of_mem_sup hRU y.2
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy]
        exact (((hUc a ha a' ha').mul_right (hUR a ha b' hb')).mul_left
          (((hUR a' ha' b hb).symm).mul_right (hRc b hb b' hb'))).eq⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        obtain ⟨a, ha, b, hb, hx⟩ := exists_mul_eq_of_mem_sup hRU x.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hx, (hUR a ha b hb).mul_pow, hUp a ha, hRp b hb, one_mul,
          Subgroup.coe_one] }

theorem card_sup_of_centralizes {U R : Subgroup D} (hRU : R ≤ centralizer (U : Set D))
    (hdisj : U ⊓ R = ⊥) : Nat.card ↥(U ⊔ R) = Nat.card U * Nat.card R := by
  let g : U × R → D := fun p => (p.1 : D) * p.2
  have hg : Function.Injective g := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h' : (a : D) * b = a' * b' := h
    have hmem : (a' : D)⁻¹ * a ∈ U ⊓ R := by
      refine mem_inf.2 ⟨mul_mem (inv_mem a'.2) a.2, ?_⟩
      have : (a' : D)⁻¹ * a = b' * (b : D)⁻¹ := by
        calc (a' : D)⁻¹ * a = (a' : D)⁻¹ * ((a : D) * b) * (b : D)⁻¹ := by group
          _ = (a' : D)⁻¹ * ((a' : D) * b') * (b : D)⁻¹ := by rw [h']
          _ = b' * (b : D)⁻¹ := by group
      rw [this]
      exact mul_mem b'.2 (inv_mem b.2)
    rw [hdisj, mem_bot, inv_mul_eq_one] at hmem
    have hb : (b : D) = b' := by
      have := h'
      rw [← hmem] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hb)
  have hrange : Set.range g = ((U ⊔ R : Subgroup D) : Set D) := by
    ext v
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact mul_mem_sup a.2 b.2
    · intro hv
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup hRU hv
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod, ← Nat.card_range_of_injective hg, hrange]
  rfl

theorem card_sup_inf_centralizer_le [Finite D] {U R : Subgroup D} {x : D}
    (hRU : R ≤ centralizer (U : Set D)) (hdisj : U ⊓ R = ⊥) (hxU : x ∈ normalizer (U : Set D))
    (hxR : x ∈ normalizer (R : Set D)) :
    Nat.card ↥((U ⊔ R) ⊓ centralizer {x}) ≤ Nat.card ↥(U ⊓ centralizer {x}) * Nat.card R := by
  let g : ↥(U ⊓ centralizer {x}) × R → D := fun p => (p.1 : D) * p.2
  have hsub : (((U ⊔ R) ⊓ centralizer {x} : Subgroup D) : Set D) ⊆ Set.range g := by
    intro v hv
    obtain ⟨hvV, hvC⟩ := mem_inf.1 hv
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup hRU hvV
    have hc : a * b * x = x * (a * b) := mem_centralizer_singleton_iff.1 hvC
    have ha' : x * a * x⁻¹ ∈ U := (mem_normalizer_iff.1 hxU a).1 ha
    have hb' : x * b * x⁻¹ ∈ R := (mem_normalizer_iff.1 hxR b).1 hb
    have hprod : (x * a * x⁻¹) * (x * b * x⁻¹) = a * b := by
      calc (x * a * x⁻¹) * (x * b * x⁻¹) = x * (a * b) * x⁻¹ := by group
        _ = a * b := by rw [← hc]; group
    have hmem : a⁻¹ * (x * a * x⁻¹) ∈ U ⊓ R := by
      refine mem_inf.2 ⟨mul_mem (inv_mem ha) ha', ?_⟩
      have : a⁻¹ * (x * a * x⁻¹) = b * (x * b * x⁻¹)⁻¹ := by
        calc a⁻¹ * (x * a * x⁻¹)
            = a⁻¹ * ((x * a * x⁻¹) * (x * b * x⁻¹)) * (x * b * x⁻¹)⁻¹ := by group
          _ = a⁻¹ * (a * b) * (x * b * x⁻¹)⁻¹ := by rw [hprod]
          _ = b * (x * b * x⁻¹)⁻¹ := by group
      rw [this]
      exact mul_mem hb (inv_mem hb')
    rw [hdisj, mem_bot, inv_mul_eq_one] at hmem
    have haC : a ∈ U ⊓ centralizer {x} := by
      refine mem_inf.2 ⟨ha, mem_centralizer_singleton_iff.2 ?_⟩
      calc a * x = (x * a * x⁻¹) * x := by rw [← hmem]
        _ = x * a := by group
    exact ⟨(⟨a, haC⟩, ⟨b, hb⟩), rfl⟩
  calc Nat.card ↥((U ⊔ R) ⊓ centralizer {x})
      = (((U ⊔ R) ⊓ centralizer {x} : Subgroup D) : Set D).ncard := Nat.card_coe_set_eq _
    _ ≤ (Set.range g).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card (Set.range g) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (↥(U ⊓ centralizer {x}) × R) :=
      Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := g))
    _ = Nat.card ↥(U ⊓ centralizer {x}) * Nat.card R := Nat.card_prod _ _

end Groups

section Ranks

variable {D : Type u} [Group D]

theorem rank_gap_of_card_sq_le [Finite D] {U R : Subgroup D} {x : D} {n : ℕ}
    (hUel : IsElementaryAbelian 2 U) (hRel : IsElementaryAbelian 2 R)
    (hRU : R ≤ centralizer (U : Set D)) (hdisj : U ⊓ R = ⊥) (hU : Nat.card U = 2 ^ n)
    (hxU : x ∈ normalizer (U : Set D)) (hxR : x ∈ normalizer (R : Set D))
    (hsq : Nat.card ↥(U ⊓ centralizer {x}) ^ 2 ≤ 2 ^ n) :
    (n + 1) / 2 + CFSG.pRank 2 ↥((U ⊔ R) ⊓ centralizer {x}) ≤ CFSG.pRank 2 ↥(U ⊔ R) := by
  have hVel := isElementaryAbelian_sup_of_centralizes hUel hRel hRU
  have hVcard := card_sup_of_centralizes hRU hdisj
  obtain ⟨r, hr⟩ := (IsElementaryAbelian.isPGroup 2 R).exists_card_eq
  obtain ⟨d, hd⟩ := ((IsElementaryAbelian.isPGroup 2 U).to_le inf_le_left :
    IsPGroup 2 ↥(U ⊓ centralizer {x})).exists_card_eq
  obtain ⟨c, hc⟩ := ((IsElementaryAbelian.isPGroup 2 ↥(U ⊔ R)).to_le inf_le_left :
    IsPGroup 2 ↥((U ⊔ R) ⊓ centralizer {x})).exists_card_eq
  have hVo : CFSG.Open.IsElemAbelian 2 (U ⊔ R) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).1 hVel
  have hCo : CFSG.Open.IsElemAbelian 2 ((U ⊔ R) ⊓ centralizer {x}) :=
    ⟨⟨⟨fun a b => Subtype.ext (show (a : D) * b = b * a from congrArg Subtype.val
      (hVo.1.is_comm.comm ⟨a, (mem_inf.1 a.2).1⟩ ⟨b, (mem_inf.1 b.2).1⟩))⟩⟩,
      fun y hy => hVo.2 y (mem_inf.1 hy).1⟩
  have hrV : CFSG.pRank 2 ↥(U ⊔ R) = n + r :=
    CFSG.LocalAnalysis.GorensteinLyons.pRank_eq_of_elementary one_lt_two hVo
      (by rw [hVcard, hU, hr, pow_add])
  have hrC : CFSG.pRank 2 ↥((U ⊔ R) ⊓ centralizer {x}) = c :=
    CFSG.LocalAnalysis.GorensteinLyons.pRank_eq_of_elementary one_lt_two hCo hc
  have hle := card_sup_inf_centralizer_le hRU hdisj hxU hxR
  rw [hc, hd, hr, ← pow_add] at hle
  have hcdr : c ≤ d + r := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  rw [hd, ← pow_mul] at hsq
  have h2d : d * 2 ≤ n := (Nat.pow_le_pow_iff_right (by norm_num)).1 hsq
  rw [hrV, hrC]
  omega

theorem card_inf_centralizer_sq_le {U P : Subgroup D} {K : Type*} [Field K] [Fintype K]
    [Algebra (ZMod 2) K] {n : ℕ} (hK : Fintype.card K = 2 ^ n) (e : Additive U ≃+ K)
    (φ : P →* (K ≃ₐ[ZMod 2] K))
    (hequiv : ∀ x : P, ∀ u v : U, (v : D) = x * u * (x : D)⁻¹ →
      e (Additive.ofMul v) = φ x (e (Additive.ofMul u)))
    (hPNU : P ≤ normalizer (U : Set D)) (x : P) (hx : φ x ≠ 1) :
    Nat.card ↥(U ⊓ centralizer {(x : D)}) ^ 2 ≤ 2 ^ n := by
  have h1 := card_fixed_sq_le_card hx
  have hconj : ∀ u : U, (x : D) * u * (x : D)⁻¹ ∈ U := fun u =>
    (mem_normalizer_iff.1 (hPNU x.2) u).1 u.2
  have hiff : ∀ u : U, (u : D) ∈ centralizer {(x : D)} ↔
      φ x (e (Additive.ofMul u)) = e (Additive.ofMul u) := by
    intro u
    rw [mem_centralizer_singleton_iff, ← hequiv x u ⟨_, hconj u⟩ rfl]
    constructor
    · intro hu
      congr 2
      apply Subtype.ext
      change (x : D) * u * (x : D)⁻¹ = u
      rw [← hu]
      group
    · intro hu
      have h2 := congrArg Subtype.val (Additive.ofMul.injective (e.injective hu))
      change (x : D) * u * (x : D)⁻¹ = u at h2
      calc (u : D) * x = ((x : D) * u * (x : D)⁻¹) * x := by rw [h2]
        _ = x * u := by group
  have h2 : Nat.card ↥(U ⊓ centralizer {(x : D)}) = Nat.card {k : K // φ x k = k} := by
    refine Nat.card_congr
      { toFun := fun y => ⟨e (Additive.ofMul ⟨y, (mem_inf.1 y.2).1⟩),
          (hiff ⟨y, (mem_inf.1 y.2).1⟩).1 (mem_inf.1 y.2).2⟩
        invFun := fun k => ⟨(Additive.toMul (e.symm k) : U),
          mem_inf.2 ⟨(Additive.toMul (e.symm k)).2, (hiff _).2 (by simpa using k.2)⟩⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun k => Subtype.ext (by simp) }
  rw [h2, ← hK, ← Nat.card_eq_fintype_card]
  exact h1

end Ranks

section Singer

variable {D : Type u} [Group D]

theorem gmsConjAct_coe_apply (X U : Subgroup D) (g : (X ⊓ normalizer (U : Set D) : Subgroup D))
    (u : U) : ((gmsConjAct X U g u : U) : D) = g * u * (g : D)⁻¹ := rfl

theorem exists_gms_singer_generator [Finite D] {X U : Subgroup D}
    (hcyc : IsCyclic (GMSNormalizerQuotient X U))
    (hreg : ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃! c : GMSNormalizerQuotient X U,
      gmsQuotConjAct X U c u = v) :
    ∃ g₀ : (X ⊓ normalizer (U : Set D) : Subgroup D),
      (∀ g : (X ⊓ normalizer (U : Set D) : Subgroup D), ∃ j : ℕ,
        gmsConjAct X U g = gmsConjAct X U g₀ ^ j) ∧
      ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃ j : ℕ, (gmsConjAct X U g₀ ^ j) u = v := by
  obtain ⟨c₀, hc₀⟩ := hcyc.exists_generator
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective c₀
  have hpow : ∀ c : GMSNormalizerQuotient X U, ∃ j : ℕ,
      (QuotientGroup.mk g₀ : GMSNormalizerQuotient X U) ^ j = c := fun c =>
    (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hc₀ c))
  have hact : ∀ g, gmsQuotConjAct X U (QuotientGroup.mk g) = gmsConjAct X U g := fun _ => rfl
  refine ⟨g₀, fun g => ?_, fun u v hu hv => ?_⟩
  · obtain ⟨j, hj⟩ := hpow (QuotientGroup.mk g)
    exact ⟨j, by rw [← hact, ← hj, map_pow, hact]⟩
  · obtain ⟨c, hc, -⟩ := hreg u v hu hv
    obtain ⟨j, rfl⟩ := hpow c
    refine ⟨j, ?_⟩
    rw [map_pow, hact] at hc
    exact hc

end Singer

section SingerField

variable {D : Type u} [Group D]

theorem gms_singer_field [Finite D] {J R X U P : Subgroup D} {n : ℕ}
    (h : GMSNormalRootData J R X U P n) :
    ∃ (K : Type u) (_ : Field K) (_ : Fintype K) (_ : Algebra (ZMod 2) K),
      Fintype.card K = 2 ^ n ∧ ∃ e : Additive U ≃+ K,
        (∀ g ∈ X ⊓ normalizer (U : Set D), ∃ c : Kˣ, ∀ u v : U, (v : D) = g * u * g⁻¹ →
          e (Additive.ofMul v) = c * e (Additive.ofMul u)) ∧
        (∀ c : Kˣ, ∃ g ∈ X ⊓ normalizer (U : Set D), ∀ u v : U, (v : D) = g * u * g⁻¹ →
          e (Additive.ofMul v) = c * e (Additive.ofMul u)) ∧
        ∃ φ : P →* (K ≃ₐ[ZMod 2] K),
          (∀ x : P, ∀ u v : U, (v : D) = x * u * (x : D)⁻¹ →
            e (Additive.ofMul v) = φ x (e (Additive.ofMul u))) ∧
          φ.ker = (P ⊓ centralizer (U : Set D)).subgroupOf P := by
  classical
  obtain ⟨hn3, -, -, ⟨hXN, hXnormal, -⟩, ⟨hUel, -, -, hUcard⟩, ⟨hcyc, -, hreg⟩,
    ⟨hPN, ⟨TP, hTP⟩, -, -, hPNU, -, -, -⟩⟩ := h
  have : IsElementaryAbelian 2 U := hUel
  have hP2 : IsPGroup 2 P := by
    have h1 : IsPGroup 2 (P.subgroupOf (normalizer (R : Set D))) := hTP ▸ TP.isPGroup'
    exact h1.of_equiv (subgroupOfEquivOfLe hPN)
  have : Nontrivial (Additive U) := by
    have h1 : 1 < Nat.card (Additive U) := by
      change 1 < Nat.card U
      rw [hUcard]
      exact Nat.one_lt_two_pow (by omega)
    exact Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨g₀, hg₀pow, hg₀trans⟩ := exists_gms_singer_generator hcyc hreg
  obtain ⟨T, hT⟩ : ∃ T : Module.End (ZMod 2) (Additive U),
      T = ((linAut (gmsConjAct X U g₀) : Additive U ≃ₗ[ZMod 2] Additive U) :
        Module.End (ZMod 2) (Additive U)) := ⟨_, rfl⟩
  have hTpow : ∀ (j : ℕ) (w : Additive U), (T ^ j) w = linAut (gmsConjAct X U g₀ ^ j) w := by
    intro j w
    rw [hT, linAut_pow_apply]
  have htrans : ∀ w w' : Additive U, w ≠ 0 → w' ≠ 0 → ∃ j : ℕ, (T ^ j) w = w' := by
    intro w w' hw hw'
    obtain ⟨j, hj⟩ := hg₀trans (Additive.toMul w) (Additive.toMul w')
      (fun h => hw (toMul_eq_one.1 h)) (fun h => hw' (toMul_eq_one.1 h))
    exact ⟨j, by rw [hTpow]; exact congrArg Additive.ofMul hj⟩
  set K := Algebra.adjoin (ZMod 2) {T} with hKdef
  have hTK : T ∈ K := Algebra.subset_adjoin (Set.mem_singleton T)
  have hTjK : ∀ j : ℕ, T ^ j ∈ K := fun j => pow_mem hTK j
  let _ : Field K := (isField_adjoin_singleton htrans).toField
  have : Finite (Module.End (ZMod 2) (Additive U)) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) (Additive U) => (f : Additive U → Additive U))
      DFunLike.coe_injective
  have hPsub : P ≤ P ⊓ normalizer (U : Set D) := le_inf le_rfl hPNU
  obtain ⟨ψ, hψ⟩ : ∃ ψ : P →* MulAut U, ψ = (gmsConjAct P U).comp (inclusion hPsub) :=
    ⟨_, rfl⟩
  have hψapply : ∀ (x : P) (u : U), ((ψ x u : U) : D) = x * u * (x : D)⁻¹ := by
    intro x u
    rw [hψ]
    rfl
  obtain ⟨u₀, hu₀, hfix⟩ : ∃ u₀ : U, u₀ ≠ 1 ∧ ∀ x : P, ψ x u₀ = u₀ := by
    let _ : MulAction P U := MulAction.compHom U ψ
    have hmod := hP2.card_modEq_card_fixedPoints U
    by_contra hcon
    push Not at hcon
    have hfp : MulAction.fixedPoints P U = {1} := by
      ext u
      rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
      constructor
      · intro hu
        by_contra hu1
        obtain ⟨x, hx⟩ := hcon u hu1
        exact hx (hu x)
      · rintro rfl x
        exact map_one (ψ x)
    rw [hfp, Nat.card_coe_set_eq, Set.ncard_singleton, hUcard] at hmod
    have h2 : 2 ^ n % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
    unfold Nat.ModEq at hmod
    omega
  set w₀ : Additive U := Additive.ofMul u₀ with hw₀def
  have hw₀ : w₀ ≠ 0 := fun h => hu₀ (toMul_eq_one.2 h)
  have hφfix : ∀ x : P, linAut (ψ x) w₀ = w₀ := fun x => by rw [hw₀def, linAut_apply, hfix x]
  have hφsymm : ∀ x : P, (linAut (ψ x)).symm w₀ = w₀ := fun x => by
    rw [LinearEquiv.symm_apply_eq, hφfix x]
  have hbij := bijective_apply_adjoin_singleton htrans hw₀
  let ev : K →+ Additive U :=
    { toFun := fun k => (k : Module.End (ZMod 2) (Additive U)) w₀
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let evA : K ≃+ Additive U := AddEquiv.ofBijective ev hbij
  have hev_mul : ∀ a b : K, evA (a * b) = (a : Module.End (ZMod 2) (Additive U)) (evA b) :=
    fun _ _ => rfl
  have hTj0 : ∀ j : ℕ, (⟨T ^ j, hTjK j⟩ : K) ≠ 0 := by
    intro j hj
    apply hw₀
    have h1 : ((⟨T ^ j, hTjK j⟩ : K) : Module.End (ZMod 2) (Additive U)) w₀ = 0 := by
      rw [hj]
      rfl
    change (T ^ j) w₀ = 0 at h1
    rw [hTpow] at h1
    exact (linAut (gmsConjAct X U g₀ ^ j)).injective (h1.trans (map_zero _).symm)
  have hscal : ∀ (j : ℕ) (g : (X ⊓ normalizer (U : Set D) : Subgroup D)),
      gmsConjAct X U g = gmsConjAct X U g₀ ^ j → ∀ u v : U, (v : D) = g * u * (g : D)⁻¹ →
        evA.symm (Additive.ofMul v) = (⟨T ^ j, hTjK j⟩ : K) * evA.symm (Additive.ofMul u) := by
    intro j g hg u v huv
    rw [AddEquiv.symm_apply_eq, hev_mul, AddEquiv.apply_symm_apply]
    change Additive.ofMul v = (T ^ j) (Additive.ofMul u)
    rw [hTpow, ← hg, linAut_apply]
    congr 1
    exact Subtype.ext huv
  have hconjT : ∀ x : P, ∃ j : ℕ, (linAut (ψ x)).conjAlgEquiv (ZMod 2) T = T ^ j := by
    intro x
    have hxg : (x : D) * g₀ * (x : D)⁻¹ ∈ X ⊓ normalizer (U : Set D) := by
      have hg₀X : (g₀ : D) ∈ X := (mem_inf.1 g₀.2).1
      have hg₀N : (g₀ : D) ∈ normalizer (U : Set D) := (mem_inf.1 g₀.2).2
      refine mem_inf.2 ⟨?_, mul_mem (mul_mem (hPNU x.2) hg₀N) (inv_mem (hPNU x.2))⟩
      exact mem_subgroupOf.1
        (hXnormal.conj_mem ⟨g₀, hXN hg₀X⟩ (mem_subgroupOf.2 hg₀X) ⟨x, hPN x.2⟩)
    obtain ⟨j, hj⟩ := hg₀pow ⟨_, hxg⟩
    refine ⟨j, LinearMap.ext fun w => ?_⟩
    rw [hTpow, ← hj]
    change linAut (ψ x) (T ((linAut (ψ x)).symm w)) = _
    rw [linAut_symm, hT]
    obtain ⟨u, rfl⟩ : ∃ u : U, Additive.ofMul u = w := ⟨Additive.toMul w, rfl⟩
    change linAut (ψ x) (linAut (gmsConjAct X U g₀) (linAut (ψ x)⁻¹ (Additive.ofMul u))) =
      linAut (gmsConjAct X U ⟨_, hxg⟩) (Additive.ofMul u)
    rw [linAut_apply, linAut_apply, linAut_apply, linAut_apply]
    congr 1
    apply Subtype.ext
    rw [← map_inv]
    simp only [hψapply, gmsConjAct_coe_apply, Subgroup.coe_inv]
    group
  have hKinv : ∀ x : P, ∀ f ∈ K, (linAut (ψ x)).conjAlgEquiv (ZMod 2) f ∈ K := by
    intro x f hf
    obtain ⟨j, hj⟩ := hconjT x
    have hle : K ≤ K.comap ((linAut (ψ x)).conjAlgEquiv (ZMod 2) :
        Module.End (ZMod 2) (Additive U) →ₐ[ZMod 2] Module.End (ZMod 2) (Additive U)) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 (by
        change (linAut (ψ x)).conjAlgEquiv (ZMod 2) T ∈ K
        rw [hj]
        exact hTjK j))
    exact hle hf
  let σ' : P → (K →ₐ[ZMod 2] K) := fun x =>
    (((linAut (ψ x)).conjAlgEquiv (ZMod 2) :
      Module.End (ZMod 2) (Additive U) →ₐ[ZMod 2] Module.End (ZMod 2) (Additive U)).comp
        K.val).codRestrict K fun k => hKinv x k k.2
  have hσ'inj : ∀ x, Function.Injective (σ' x) := by
    intro x a b hab
    apply Subtype.ext
    exact ((linAut (ψ x)).conjAlgEquiv (ZMod 2)).injective (congrArg Subtype.val hab)
  let σ : P → (K ≃ₐ[ZMod 2] K) := fun x =>
    AlgEquiv.ofBijective (σ' x) (Finite.injective_iff_bijective.1 (hσ'inj x))
  let φ : P →* (K ≃ₐ[ZMod 2] K) :=
    { toFun := σ
      map_one' := by
        apply AlgEquiv.ext
        intro k
        apply Subtype.ext
        apply LinearMap.ext
        intro w
        change linAut (ψ 1) ((k : Module.End (ZMod 2) (Additive U)) ((linAut (ψ 1)).symm w)) =
          (k : Module.End (ZMod 2) (Additive U)) w
        rw [map_one, map_one]
        rfl
      map_mul' := by
        intro x y
        apply AlgEquiv.ext
        intro k
        apply Subtype.ext
        apply LinearMap.ext
        intro w
        change linAut (ψ (x * y)) ((k : Module.End (ZMod 2) (Additive U))
            ((linAut (ψ (x * y))).symm w)) =
          linAut (ψ x) (linAut (ψ y) ((k : Module.End (ZMod 2) (Additive U))
            ((linAut (ψ y)).symm ((linAut (ψ x)).symm w))))
        rw [map_mul, map_mul]
        rfl }
  have hφw : ∀ (x : P) (k : K) (w : Additive U),
      ((φ x k : K) : Module.End (ZMod 2) (Additive U)) w =
        linAut (ψ x) ((k : Module.End (ZMod 2) (Additive U)) ((linAut (ψ x)).symm w)) :=
    fun _ _ _ => rfl
  refine ⟨K, inferInstance, Fintype.ofFinite K, inferInstance, ?_, evA.symm, ?_, ?_, φ, ?_, ?_⟩
  ·
    rw [Fintype.card_eq_nat_card, Nat.card_congr evA.toEquiv]
    exact hUcard
  ·
    intro g hg
    obtain ⟨j, hj⟩ := hg₀pow ⟨g, hg⟩
    refine ⟨Units.mk0 _ (hTj0 j), fun u v huv => ?_⟩
    rw [Units.val_mk0]
    exact hscal j ⟨g, hg⟩ hj u v huv
  ·
    intro c
    have hc0 : ((c : K) : Module.End (ZMod 2) (Additive U)) ≠ 0 := fun h0 =>
      c.ne_zero (Subtype.ext h0)
    obtain ⟨j, hj⟩ := exists_pow_eq_of_mem_adjoin_singleton htrans (c : K).2 hc0
    refine ⟨((g₀ ^ j : (X ⊓ normalizer (U : Set D) : Subgroup D)) : D), (g₀ ^ j).2,
      fun u v huv => ?_⟩
    have hcj : (c : K) = ⟨T ^ j, hTjK j⟩ := Subtype.ext hj.symm
    rw [hcj]
    exact hscal j (g₀ ^ j) (map_pow _ _ _) u v huv
  ·
    intro x u v huv
    rw [AddEquiv.symm_apply_eq]
    change Additive.ofMul v = ((φ x (evA.symm (Additive.ofMul u)) : K) :
      Module.End (ZMod 2) (Additive U)) w₀
    rw [hφw, hφsymm x]
    change Additive.ofMul v = linAut (ψ x) (evA (evA.symm (Additive.ofMul u)))
    rw [AddEquiv.apply_symm_apply, linAut_apply]
    congr 1
    apply Subtype.ext
    rw [hψapply]
    exact huv
  ·
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    constructor
    · intro hx
      refine ⟨x.2, mem_centralizer_iff.2 fun u hu => ?_⟩
      have hfixW : ∀ w : Additive U, linAut (ψ x) w = w := by
        intro w
        obtain ⟨k, rfl⟩ := evA.surjective w
        have h1 : φ x k = k := by
          rw [hx]
          rfl
        have h2 := congrArg (fun k' : K => (k' : Module.End (ZMod 2) (Additive U)) w₀) h1
        rw [hφw, hφsymm x] at h2
        exact h2
      have h3 := hfixW (Additive.ofMul ⟨u, hu⟩)
      rw [linAut_apply] at h3
      have h4 := congrArg Subtype.val (Additive.ofMul.injective h3)
      rw [hψapply] at h4
      calc u * x = ((x : D) * u * (x : D)⁻¹) * x := by rw [h4]
        _ = x * u := by group
    · rintro ⟨-, hxC⟩
      have hψ1 : ψ x = 1 := by
        ext u
        rw [hψapply, MulAut.one_apply, ← mem_centralizer_iff.1 hxC u u.2]
        group
      apply AlgEquiv.ext
      intro k
      apply Subtype.ext
      apply LinearMap.ext
      intro w
      rw [hφw, hψ1, map_one]
      rfl

end SingerField

section Main

variable {D : Type u} [Group D]

theorem gms_normal_root_singer_action_and_weak_closure [Finite D] {J R X U P : Subgroup D}
    {n : ℕ} (h : GMSNormalRootData J R X U P n) :
    (∃ (K : Type u) (_ : Field K) (_ : Fintype K) (_ : Algebra (ZMod 2) K),
      Fintype.card K = 2 ^ n ∧ ∃ e : Additive U ≃+ K,
        (∀ g ∈ X ⊓ normalizer (U : Set D), ∃ c : Kˣ, ∀ u v : U, (v : D) = g * u * g⁻¹ →
          e (Additive.ofMul v) = c * e (Additive.ofMul u)) ∧
        (∀ c : Kˣ, ∃ g ∈ X ⊓ normalizer (U : Set D), ∀ u v : U, (v : D) = g * u * g⁻¹ →
          e (Additive.ofMul v) = c * e (Additive.ofMul u)) ∧
        ∃ φ : P →* (K ≃ₐ[ZMod 2] K),
          (∀ x : P, ∀ u v : U, (v : D) = x * u * (x : D)⁻¹ →
            e (Additive.ofMul v) = φ x (e (Additive.ofMul u))) ∧
          φ.ker = (P ⊓ centralizer (U : Set D)).subgroupOf P ∧
          φ.ker = (U ⊔ R).subgroupOf P) ∧
    ((U ⊔ R).subgroupOf P).Normal ∧
    (∀ [((U ⊔ R).subgroupOf P).Normal], IsCyclic (P ⧸ (U ⊔ R).subgroupOf P) ∧
      Nat.card (P ⧸ (U ⊔ R).subgroupOf P) ∣ n ∧
      CFSG.pRank 2 (P ⧸ (U ⊔ R).subgroupOf P) ≤ 1) ∧
    2 ≤ (n + 1) / 2 ∧
    (∀ x ∈ P, x ∉ U ⊔ R →
      (n + 1) / 2 + CFSG.pRank 2 ↥((U ⊔ R) ⊓ centralizer {x}) ≤ CFSG.pRank 2 ↥(U ⊔ R)) ∧
    P ⊓ centralizer ((U ⊔ R : Subgroup D) : Set D) = U ⊔ R ∧
    (∀ g : D, CFSG.conjugate (U ⊔ R) g ≤ P → CFSG.conjugate (U ⊔ R) g = U ⊔ R) ∧
    ((∃ T : Sylow 2 D, (T : Subgroup D) = P) →
      IsStronglyClosedIn P ((U ⊔ R : Subgroup D) : Set D)) ∧
    (gmsConjAct X U).ker =
      (X ⊓ centralizer (U : Set D)).subgroupOf (X ⊓ normalizer (U : Set D)) ∧
    X ⊓ normalizer (U : Set D) ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) ∧
    X ⊓ normalizer (U : Set D) ⊓ centralizer ((U ⊔ R : Subgroup D) : Set D) =
      X ⊓ centralizer (U : Set D) := by
  classical
  obtain ⟨K, _, _, _, hKcard, e, hsc1, hsc2, φ, hequiv, hker⟩ := gms_singer_field h
  obtain ⟨hn3, -, ⟨hRel, -, -⟩, ⟨-, -, hXC⟩, ⟨hUel, hUX, -, hUcard⟩, -,
    ⟨hPN, ⟨TP, hTP⟩, hUP, hRP, hPNU, hUR, hCPU, hVn⟩⟩ := h
  have hRU : R ≤ centralizer (U : Set D) := le_centralizer_iff.1 (hUX.trans hXC)
  have hVel := isElementaryAbelian_sup_of_centralizes hUel hRel hRU
  have hVP : U ⊔ R ≤ P := sup_le hUP hRP
  have hP2 : IsPGroup 2 P := by
    have h1 : IsPGroup 2 (P.subgroupOf (normalizer (R : Set D))) := hTP ▸ TP.isPGroup'
    exact h1.of_equiv (subgroupOfEquivOfLe hPN)
  have hker' : φ.ker = (U ⊔ R).subgroupOf P := by rw [hker, hCPU]
  have hquot : ∀ [((U ⊔ R).subgroupOf P).Normal], IsCyclic (P ⧸ (U ⊔ R).subgroupOf P) ∧
      Nat.card (P ⧸ (U ⊔ R).subgroupOf P) ∣ n ∧
      CFSG.pRank 2 (P ⧸ (U ⊔ R).subgroupOf P) ≤ 1 := by
    intro _
    obtain ⟨hcyc, hdvd⟩ := isCyclic_quotient_of_ker_eq hKcard φ hker'
    exact ⟨hcyc, hdvd, pRank_two_le_one_of_isCyclic⟩
  have hgap : ∀ x ∈ P, x ∉ U ⊔ R →
      (n + 1) / 2 + CFSG.pRank 2 ↥((U ⊔ R) ⊓ centralizer {x}) ≤ CFSG.pRank 2 ↥(U ⊔ R) := by
    intro x hx hxV
    have hφx : φ ⟨x, hx⟩ ≠ 1 := fun h1 => hxV (by
      have hmem : (⟨x, hx⟩ : P) ∈ φ.ker := h1
      rw [hker'] at hmem
      exact hmem)
    exact rank_gap_of_card_sq_le hUel hRel hRU hUR hUcard (hPNU hx) (hPN hx)
      (card_inf_centralizer_sq_le hKcard e φ hequiv hPNU ⟨x, hx⟩ hφx)
  have hcrit := CFSG.LocalAnalysis.GorensteinLyons.elementary_strict_rank_strong_closure_criterion
    hP2 hVP hVel fun x hx hxV => by
      have h1 := (@hquot hVn).2.2
      have h2 := hgap x hx hxV
      omega
  have hCPV : P ⊓ centralizer ((U ⊔ R : Subgroup D) : Set D) = U ⊔ R := by
    apply le_antisymm
    · exact (inf_le_inf_left P (centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))).trans
        hCPU.le
    · exact le_inf hVP (le_centralizer_iff_isMulCommutative.2 hVel.toIsMulCommutative)
  have hkerU : (gmsConjAct X U).ker =
      (X ⊓ centralizer (U : Set D)).subgroupOf (X ⊓ normalizer (U : Set D)) := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    constructor
    · intro hg
      refine ⟨(mem_inf.1 g.2).1, mem_centralizer_iff.2 fun u hu => ?_⟩
      have h1 := congrArg Subtype.val (MulEquiv.congr_fun hg ⟨u, hu⟩)
      rw [gmsConjAct_coe_apply, MulAut.one_apply] at h1
      calc u * g = ((g : D) * u * (g : D)⁻¹) * g := by rw [h1]
        _ = g * u := by group
    · rintro ⟨-, hgC⟩
      ext u
      rw [gmsConjAct_coe_apply, MulAut.one_apply, ← mem_centralizer_iff.1 hgC u u.2]
      group
  have hNV : X ⊓ normalizer (U : Set D) ≤ normalizer ((U ⊔ R : Subgroup D) : Set D) := by
    intro g hg
    have hgR : g ∈ normalizer (R : Set D) := centralizer_le_normalizer _ (hXC (mem_inf.1 hg).1)
    exact inf_normalizer_le_normalizer_sup U R (mem_inf.2 ⟨(mem_inf.1 hg).2, hgR⟩)
  have hkerV : X ⊓ normalizer (U : Set D) ⊓ centralizer ((U ⊔ R : Subgroup D) : Set D) =
      X ⊓ centralizer (U : Set D) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgXN, hgC⟩ := mem_inf.1 hg
      exact mem_inf.2 ⟨(mem_inf.1 hgXN).1,
        centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hgC⟩
    · intro g hg
      obtain ⟨hgX, hgC⟩ := mem_inf.1 hg
      refine mem_inf.2 ⟨mem_inf.2 ⟨hgX, centralizer_le_normalizer _ hgC⟩, ?_⟩
      have hgR : g ∈ centralizer (R : Set D) := hXC hgX
      have hle : U ⊔ R ≤ centralizer {g} :=
        sup_le (fun u hu => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hgC u hu))
          (fun r hr => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hgR r hr))
      exact mem_centralizer_iff.2 fun v hv => mem_centralizer_singleton_iff.1 (hle hv)
  exact ⟨⟨K, inferInstance, inferInstance, inferInstance, hKcard, e, hsc1, hsc2, φ, hequiv, hker,
    hker'⟩, hVn, hquot, by omega, hgap, hCPV, hcrit.1, hcrit.2.2, hkerU, hNV, hkerV⟩

end Main

end CFSG.LocalAnalysis.SteinbergBT

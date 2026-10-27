module

public import CFSG.Quasithin.EmptyFaithful.R3c17B
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.Quasithin.R3c17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6
  CFSG.Quasithin.R3c16 CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c15
  CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.B113Lie
open scoped commutatorElement Pointwise

section Transport

theorem mem_normalizer_map_of_mem {X Y : Type*} [Group X] [Group Y] (ψ : X →* Y) {V : Subgroup X}
    {t : X} (ht : t ∈ Subgroup.normalizer (V : Set X)) :
    ψ t ∈ Subgroup.normalizer ((V.map ψ : Subgroup Y) : Set Y) := by
  have hti : t⁻¹ ∈ Subgroup.normalizer (V : Set X) := inv_mem ht
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨?_, ?_⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨t * v * t⁻¹, (Subgroup.mem_normalizer_iff.1 ht v).1 hv, by simp [map_mul, map_inv]⟩
  · rintro ⟨v, hv, hvh⟩
    refine ⟨t⁻¹ * v * t, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 hti v).1 hv
      simpa using this
    · have : h = (ψ t)⁻¹ * ψ v * ψ t := by
        rw [hvh]
        group
      rw [this]
      simp [map_mul, map_inv]

end Transport

section Facts

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem four_le_card_orbitField {f : ℕ} (hf : 2 ≤ f) (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (a : Fin TwistTag.D4.foldedTag.rank) :
    4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom a) := by
  have hposall : ∀ a : Fin TwistTag.D4.foldedTag.rank, 1 ≤ (TwistTag.D4.orbit a).card := by
    decide
  have h2f : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hσ1 : ∀ c, σ.toRingHom c = c ^ ((2 ^ f) ^ 1) := fun c => by
    rw [pow_one]
    exact hσ c
  have hc := card_orbitField_D4_orientation Nat.prime_two (by omega) hK (r := 1) (Or.inl rfl) hσ1 a
  rw [hc]
  have hpos : 1 ≤ (TwistTag.D4.orbit a).card := hposall a
  calc 4 ≤ 2 ^ f := h2f
    _ = (2 ^ f) ^ 1 := (pow_one _).symm
    _ ≤ (2 ^ f) ^ (TwistTag.D4.orbit a).card := Nat.pow_le_pow_right (by omega) hpos

end Facts

section Main

theorem centralScalar_triality
    {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : ChevalleyExceptionalModel X .trialityD4 2 f) : CentralScalar X := by
  intro T V hT hVT hV4 hTV y hyV k hk hyn
  classical
  obtain ⟨K, hF, hFin, σ, φ, hK, hσ, hφ, -, -⟩ := even_rank_two_residual_triality hX hT
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfm : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ.toRingHom ^ 3 = 1 := RingHom.ext fun c => by
    rw [ringHom_pow_three_apply]
    exact ringEquiv_cube_apply_eq hK hσ c
  have h4 := four_le_card_orbitField hf σ hK hσ
  obtain ⟨hT2, -⟩ := K1.isSylowTwoOf_top_iff.mp hT
  let ψ : X →* ModGL TwistTag.D4.tag K :=
    (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype.comp φ.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp φ.injective
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hTU : T.map ψ = graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    have : T.map ψ = (T.map φ.toMonoidHom).map
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype :=
      (Subgroup.map_map _ _ _).symm
    rw [this, hφ]
    exact Subgroup.map_subgroupOf_eq_of_le hUC
  have hψC : ∀ x : X, ψ x ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun x => (φ x).2
  have hV'U : V.map ψ ≤ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    hTU ▸ Subgroup.map_mono hVT
  have hV'4 : Nat.card (V.map ψ) = 4 := by
    rw [← hV4]
    exact (Nat.card_congr (V.equivMapOfInjective ψ hψ).toEquiv).symm
  have hUN : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      Subgroup.normalizer ((V.map ψ : Subgroup (ModGL TwistTag.D4.tag K)) :
        Set (ModGL TwistTag.D4.tag K)) := by
    rw [← hTU]
    rintro _ ⟨t, ht, rfl⟩
    exact mem_normalizer_map_of_mem ψ (hTV ht)
  have hMne : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
      Subgroup.normalizer ((V.map ψ : Subgroup (ModGL TwistTag.D4.tag K)) :
        Set (ModGL TwistTag.D4.tag K)) ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    intro hMC'
    have hCN : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤
        Subgroup.normalizer ((V.map ψ : Subgroup (ModGL TwistTag.D4.tag K)) :
          Set (ModGL TwistTag.D4.tag K)) := fun g hg =>
      (show g ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓ Subgroup.normalizer
        ((V.map ψ : Subgroup (ModGL TwistTag.D4.tag K)) : Set (ModGL TwistTag.D4.tag K)) from
          hMC'.symm ▸ hg).2
    have hV'C : V.map ψ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := hV'U.trans hUC
    have hnorm : ((V.map ψ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hV'C).2 hCN
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
    obtain ⟨-, ⟨PV, hPV⟩, hUV, -⟩ := exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀
    have hU₁2 : IsPGroup 2 ↥((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := hφ ▸ hT2.map φ.toMonoidHom
    have hV₁U : (V.map ψ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤
        (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun x hx => hV'U hx
    have hV₁2 : IsPGroup 2 ↥((V.map ψ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
      hU₁2.to_le hV₁U
    have hle := hV₁2.le_sylow_of_normal PV
    rw [hPV] at hle
    have hbot : V.map ψ ≤ ⊥ := by
      intro x hx
      have hxU : x ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := hV'U hx
      have hxV : x ∈ graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom :=
        hle (show (⟨x, hV'C hx⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
          (V.map ψ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) from hx)
      have : x ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓
          graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom := ⟨hxU, hxV⟩
      rwa [hUV] at this
    have h1 : Nat.card (V.map ψ) = 1 := by
      have : V.map ψ = ⊥ := le_bot_iff.1 hbot
      rw [this]
      exact Subgroup.card_bot
    omega
  have hyM : ψ y ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
      Subgroup.normalizer ((V.map ψ : Subgroup (ModGL TwistTag.D4.tag K)) :
        Set (ModGL TwistTag.D4.tag K)) := ⟨hψC y, mem_normalizer_map_of_mem ψ hyV⟩
  have hk' : (ψ y) ^ (3 ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have hyn' : ¬ ∀ v ∈ V.map ψ, ψ y * v = v * ψ y := by
    intro h
    apply hyn
    intro v hv
    apply hψ
    rw [map_mul, map_mul]
    exact h (ψ v) (Subgroup.mem_map_of_mem ψ hv)
  obtain ⟨ha, hb⟩ := triality_core σ hσ3 h4 hV'U hV'4 inf_le_left
    (le_inf hUC hUN) hMne inf_le_right hyM hk' hyn'
  have hcentral : ∀ v ∈ V, ∀ q ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
      q * ψ v = ψ v * q := fun v hv q hq => ha q hq (ψ v) (Subgroup.mem_map_of_mem ψ hv)
  constructor
  · intro v hv t ht
    apply hψ
    rw [map_mul, map_mul]
    exact ha (ψ t) (hTU ▸ Subgroup.mem_map_of_mem ψ ht) (ψ v) (Subgroup.mem_map_of_mem ψ hv)
  · intro g hg z hzT hzc hz1 hgz v hv
    obtain ⟨l, hl⟩ := hb (ψ g) ⟨hψC g, mem_normalizer_map_of_mem ψ hg⟩
    have hzU : ψ z ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
      hTU ▸ Subgroup.mem_map_of_mem ψ hzT
    obtain ⟨c, hc⟩ := triality_center_x6' σ hσ3 hzU (fun q hq => by
      rw [← hTU] at hq
      obtain ⟨t, ht, rfl⟩ := hq
      rw [← map_mul, ← map_mul, hzc t ht])
    have hc0 : c ≠ 0 := by
      intro h0
      apply hz1
      apply hψ
      rw [hc, h0, map_one]
      exact pinnedX_zero _ _ _
    have hl1 : l = 1 := by
      have h1 := hl c
      rw [← hc] at h1
      have h2 : ψ g * ψ z * (ψ g)⁻¹ = ψ z := by
        rw [← map_mul, ← map_inv, ← map_mul, hgz]
        group
      rw [h2, hc] at h1
      have h3 := pinnedX_injective (τ := TwistTag.D4.tag) (R := K) (trialityRoot 5) h1
      have h4' : (c : K) ≠ 0 := fun h => hc0 (Subtype.ext h)
      exact (mul_eq_right₀ h4').1 h3.symm
    obtain ⟨d, hd⟩ := triality_center_x6' σ hσ3 (hV'U (Subgroup.mem_map_of_mem ψ hv))
      (fun q hq => hcentral v hv q hq)
    apply hψ
    rw [map_mul, map_mul]
    have h5 : ψ g * ψ v * (ψ g)⁻¹ = ψ v := by
      rw [hd, hl d, hl1, one_mul]
    calc ψ g * ψ v = (ψ g * ψ v * (ψ g)⁻¹) * ψ g := by group
      _ = ψ v * ψ g := by rw [h5]

end Main

section Elim

theorem zeta_facts_triality
    {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 1 ≤ f)
    (hX : ChevalleyExceptionalModel X .trialityD4 2 f) {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) :
    (∀ β : X ≃* X, (∀ q ∈ T, β q = q) → ∃ x : X, ∀ y : X, β y = x⁻¹ * y * x) ∧
    (∀ φ : MulAut X, (∀ u ∈ T, φ u = u) → Odd (orderOf φ) → φ = 1) ∧
    (∀ g : X, (∀ y : X, g * y = y * g) → g = 1) := by
  obtain ⟨K, hF, hFin, σ, φ, hK, hσ, hφ, -, -⟩ := even_rank_two_residual_triality hX hT
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  refine ⟨(SylowCentralizingAutInner.of_mulEquiv φ
    (sylowCentralizingAutInner_triality σ hf hK hσ)) T hT, (d4_sylowFacts hf hX hT).2.2, ?_⟩
  intro g hg
  have hgc : φ g ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Subgroup.mem_center_iff.2 fun z => by
      obtain ⟨x, rfl⟩ := φ.surjective z
      rw [← map_mul, ← map_mul, hg x]
  rw [exceptional_fixed_center_trivial TwistTag.D4 K σ] at hgc
  exact φ.injective (by rw [map_one]; exact Subgroup.mem_bot.1 hgc)

theorem not_elConfig_of_triality_scalar
    {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : ChevalleyExceptionalModel X .trialityD4 2 f) : ¬ ElConfig X := by
  rintro ⟨T, V, H, ζ, hT, hd⟩
  obtain ⟨hA, hOdd, hZ⟩ := zeta_facts_triality (by omega) hX hT
  exact not_elData_of_centralScalar hT hA hOdd hZ (centralScalar_triality hf hX) hd

variable {G : Type} [Group G] [Finite G]

theorem elim15343_of_triality_scalar
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 f) : False :=
  not_elConfig_of_triality_scalar hf h (elConfig_of_ctx1 c o hN hYL)

theorem cl15335_case2_of_triality_scalar
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L)
    (hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
      Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) {f : ℕ} (hf : 2 ≤ f)
    (h : ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 f) : False :=
  not_elConfig_of_triality_scalar hf h (elConfig_of_ctx2 h113 c hN hYL hU)

end Elim

end CFSG.Quasithin.R3c17

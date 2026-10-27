module

public import CFSG.Quasithin.EmptyFaithful.R3c16TriA
public import CFSG.Quasithin.EmptyFaithful.R3c16ReeB
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder

public section

namespace CFSG.Quasithin.R3c16

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6

theorem not_three_dvd_two_pow_cube_sub_one {f : ℕ} (hf : Odd f) : ¬ 3 ∣ (2 ^ f) ^ 3 - 1 := by
  obtain ⟨b, rfl⟩ := hf
  have : (2 ^ (2 * b + 1)) ^ 3 = 2 ^ (2 * (3 * b + 1) + 1) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [this]
  exact not_three_dvd_two_pow_sub_one _

section StepC

theorem noThreeAct_gamma_tri
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (h3 : ¬ 3 ∣ Nat.card K - 1)
    (h4 : ∀ a : Fin TwistTag.D4.foldedTag.rank,
      4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom a))
    {X : Type} [Group X] (φ : X ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {T V : Subgroup X} (hT2 : IsPGroup 2 ↥T)
    (hφ : T.map φ.toMonoidHom = (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hVT : V ≤ T) (hV4 : Nat.card V = 4) (hTV : T ≤ Subgroup.normalizer (V : Set X)) {y : X}
    (hyV : y ∈ Subgroup.normalizer (V : Set X)) {k : ℕ} (hk : y ^ (3 ^ k) = 1) :
    ∀ v ∈ V, y * v = v * y := by
  classical
  by_cases hy1 : y = 1
  · intro v _
    rw [hy1, one_mul, mul_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUN : (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤
      Subgroup.normalizer ((V.map φ.toMonoidHom :
        Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    rw [← hφ]
    rintro _ ⟨t, ht, rfl⟩
    exact (R3c11.mem_normalizer_map_equiv_iff φ V t).mpr (hTV ht)
  have hyN : φ y ∈ Subgroup.normalizer ((V.map φ.toMonoidHom :
      Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
    (R3c11.mem_normalizer_map_equiv_iff φ V y).mpr hyV
  have hV₁U : V.map φ.toMonoidHom ≤ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := hφ ▸ Subgroup.map_mono hVT
  have hV₁4 : Nat.card (V.map φ.toMonoidHom) = 4 := by
    rw [← hV4]
    exact (Nat.card_congr (V.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv).symm
  have hU₁2 : IsPGroup 2 ↥((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := hφ ▸ hT2.map φ.toMonoidHom
  have hN1 : Subgroup.normalizer ((V.map φ.toMonoidHom :
      Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) ≠ ⊤ := by
    intro htop
    have hnorm : (V.map φ.toMonoidHom).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
    obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
    obtain ⟨-, ⟨PV, hPV⟩, hUV, -⟩ := exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀
    have hV₁2 : IsPGroup 2 ↥(V.map φ.toMonoidHom) := hU₁2.to_le hV₁U
    have hle : V.map φ.toMonoidHom ≤ (PV : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
      hV₁2.le_sylow_of_normal PV
    rw [hPV] at hle
    have hbot : V.map φ.toMonoidHom ≤ ⊥ := by
      intro x hx
      have hxU : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
        hV₁U hx
      have hxV : (x : ModGL TwistTag.D4.tag K) ∈
          graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom := hle hx
      have : (x : ModGL TwistTag.D4.tag K) ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊓
          graphFixedNegUnipotent TwistTag.D4 K σ.toRingHom := ⟨hxU, hxV⟩
      rw [hUV, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    have h1 : Nat.card (V.map φ.toMonoidHom) = 1 := by
      have : V.map φ.toMonoidHom = ⊥ := le_bot_iff.1 hbot
      rw [this]
      exact Subgroup.card_bot
    omega
  have hMC : (Subgroup.normalizer ((V.map φ.toMonoidHom :
      Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := Subgroup.map_subtype_le _
  have hUM : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      (Subgroup.normalizer ((V.map φ.toMonoidHom :
        Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hUC]
    exact Subgroup.map_mono hUN
  have hMne : (Subgroup.normalizer ((V.map φ.toMonoidHom :
      Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype ≠
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := by
    intro h
    apply hN1
    apply Subgroup.map_injective (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact h
  have hyM : ((φ y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      ModGL TwistTag.D4.tag K) ∈ (Subgroup.normalizer ((V.map φ.toMonoidHom :
        Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype :=
    Subgroup.mem_map_of_mem _ hyN
  have hφk : (φ y) ^ (3 ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have hk' : ((φ y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      ModGL TwistTag.D4.tag K) ^ (3 ^ k) = 1 := by
    rw [← Subgroup.coe_pow, hφk]
    exact Subgroup.coe_one _
  have hy1' : ((φ y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
      ModGL TwistTag.D4.tag K) ≠ 1 := by
    intro h
    apply hy1
    apply φ.injective
    rw [map_one]
    exact Subtype.ext h
  obtain ⟨L, hperf, hLM, hyUL⟩ :=
    triality_threeElement_mem_sup_block σ h3 h4 hMC hUM hMne hyM hk' hy1'
  have hLC : L ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := hLM.trans hMC
  have hyUL' : φ y ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊔
      L.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    rw [← Subgroup.subgroupOf_sup hUC hLC]
    exact hyUL
  have hLN : L.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤
      Subgroup.normalizer ((V.map φ.toMonoidHom :
        Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    intro l hl
    have hlM : (l : ModGL TwistTag.D4.tag K) ∈ (Subgroup.normalizer ((V.map φ.toMonoidHom :
        Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map
            (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype := hLM hl
    obtain ⟨n, hn, hnl⟩ := hlM
    have : n = l := Subtype.ext hnl
    rw [← this]
    exact hn
  have hL₁perf : Group.IsPerfect
      ↥(L.subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
    have := hperf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLC).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have key := centralizes_of_mem_sup_perfect (V := V.map φ.toMonoidHom) le_rfl hV₁4
    hU₁2 hUN hLN hL₁perf hyUL' hφk
  intro v hv
  apply φ.injective
  rw [map_mul, map_mul]
  exact key (φ v) ⟨v, hv, rfl⟩

theorem noThreeAct_triality
    {X : Type} [Group X] [Finite X] {f : ℕ} (hodd : Odd f) (hf : 3 ≤ f)
    (hX : ChevalleyExceptionalModel X .trialityD4 2 f)
    {T V : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hVT : V ≤ T) (hV4 : Nat.card V = 4)
    (hTV : T ≤ Subgroup.normalizer (V : Set X)) {y : X}
    (hyV : y ∈ Subgroup.normalizer (V : Set X)) {k : ℕ} (hk : y ^ (3 ^ k) = 1) :
    ∀ v ∈ V, y * v = v * y := by
  obtain ⟨K, hF, hFin, σ, φ, hK, hσ, hφ, -, -⟩ := even_rank_two_residual_triality hX hT
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have h3 : ¬ 3 ∣ Nat.card K - 1 := by
    rw [hK]
    exact not_three_dvd_two_pow_cube_sub_one hodd
  have h2f : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hposall : ∀ a : Fin TwistTag.D4.foldedTag.rank, 1 ≤ (TwistTag.D4.orbit a).card := by
    decide
  have h4 : ∀ a : Fin TwistTag.D4.foldedTag.rank,
      4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom a) := by
    intro a
    have hσ1 : ∀ c, σ.toRingHom c = c ^ ((2 ^ f) ^ 1) := fun c => by
      rw [pow_one]
      exact hσ c
    have hc := card_orbitField_D4_orientation Nat.prime_two (by omega) hK (r := 1) (Or.inl rfl) hσ1 a
    rw [hc]
    have hpos : 1 ≤ (TwistTag.D4.orbit a).card := hposall a
    calc 4 ≤ 2 ^ f := by omega
      _ = (2 ^ f) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ f) ^ (TwistTag.D4.orbit a).card :=
        Nat.pow_le_pow_right (by omega) hpos
  exact noThreeAct_gamma_tri σ h3 h4 φ (K1.isSylowTwoOf_top_iff.mp hT).1 hφ hVT hV4 hTV hyV hk

end StepC

end CFSG.Quasithin.R3c16

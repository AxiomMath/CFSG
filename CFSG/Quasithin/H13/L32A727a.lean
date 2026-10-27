module

import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.H13.L32A705a

public section

namespace CFSG.Quasithin.H13.L32A.R727

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

abbrev Concl (T L V H : Subgroup G) : Prop :=
  CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ ∨
    CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) = modO2Image H (l1 T L V)

@[expose] def pre (H : Subgroup G) (K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Subgroup G :=
  (K.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype

omit [Finite G] in
theorem mem_pCoreOf_iff (x : ↥H) : (x : G) ∈ pCoreOf 2 H ↔ x ∈ CFSG.pCore 2 ↥H :=
  CFSG.mem_openPCoreOf_iff x

omit [Finite G] in
theorem mem_pre {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (x : ↥H) :
    (x : G) ∈ pre H K ↔ QuotientGroup.mk' (CFSG.pCore 2 ↥H) x ∈ K := by
  exact (Subgroup.mem_map_iff_mem H.subtype_injective).trans Subgroup.mem_comap

omit [Finite G] in
theorem pre_le (K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : pre H K ≤ H := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

omit [Finite G] in
theorem pre_mono {K₁ K₂ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (h : K₁ ≤ K₂) : pre H K₁ ≤ pre H K₂ :=
  Subgroup.map_mono (Subgroup.comap_mono h)

omit [Finite G] in
theorem pCoreOf_le_pre (K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : pCoreOf 2 H ≤ pre H K := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe] at hx
  refine (mem_pre x).mpr ?_
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [h1]
  exact K.one_mem

omit [Finite G] in
theorem le_normalizer_pre {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hK : K.Normal) :
    H ≤ Subgroup.normalizer (pre H K : Set G) := by
  have : ((pre H K).subgroupOf H).Normal := by
    rw [pre, ← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact hK.comap _
  exact Subgroup.le_normalizer_of_normal_subgroupOf (pre_le K)

omit [Finite G] in
theorem modO2Image_pre (K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : modO2Image H (pre H K) = K := by
  rw [modO2Image, pre, ← Subgroup.comap_subtype,
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) K

omit [Finite G] in
theorem le_pre_of_le {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} {X : Subgroup G} (hXH : X ≤ H)
    (hX : modO2Image H X ≤ K) : X ≤ pre H K := fun x hx =>
  (mem_pre ⟨x, hXH hx⟩).mpr (hX ⟨⟨x, hXH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)

omit [Finite G] in
theorem pow_mem_of_isPGroup {p : ℕ} {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hK : IsPGroup p ↥K)
    {g : G} (hg : g ∈ pre H K) : ∃ k : ℕ, g ^ p ^ k ∈ pCoreOf 2 H := by
  obtain ⟨x, hx, rfl⟩ := hg
  obtain ⟨k, hk⟩ := hK ⟨_, hx⟩
  refine ⟨k, ?_⟩
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (x ^ p ^ k) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hk
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  rw [← mem_pCoreOf_iff] at h2
  simpa using h2

theorem l1T_le_M (hyp : Hyp147 G T L V) (h1332 : Stmt13_3_2) :
    l1 T L V ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
  sup_le ((oTwoUpper_le _).trans (inf_le_left.trans Subgroup.le_normalizer))
    (h1332 G T L hyp.hyp.h13 L hyp.hyp.h13.faithful).2.1.1

theorem setting_of_le (S : Setting147 G T L V H) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {X : Subgroup G} (hLX : l1 T L V ⊔ T ≤ X) (hXH : X ≤ H)
    (hXM : ¬ X ≤ Subgroup.normalizer (L : Set G)) : Setting147 G T L V X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV1 := Hyp147.isTSub_V1 S.hyp (stmtL32NModule_of_inputs h1332 h1334)
  have hXG : X ≤ A6.g1 T V := hXH.trans S.hz.2.1
  have hV1T : fsuV1 T V ≤ T := by
    have hZ : quasithinOmegaOneCenter T ≤ T :=
      (Subgroup.closure_le _).mpr fun _ hz => hz.1.1
    exact inf_le_right.trans hZ
  have hV1O : fsuV1 T V ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 (hV1T.trans (le_sup_right.trans hLX)) hXG
      (IsPGroup.of_card hV1.2.1)
  have hO2 : pCoreOf 2 X ≠ ⊥ := by
    intro h
    have : Nat.card ↥(fsuV1 T V) = 1 := by
      rw [h, le_bot_iff] at hV1O
      rw [hV1O, Subgroup.card_bot]
    rw [hV1.2.1] at this
    norm_num at this
  exact ⟨S.hyp, ⟨⟨hLX, hO2⟩, hXG, hXM⟩⟩

theorem le_M_of_concl {H₀ : Subgroup G} (S₀ : Setting147 G T L V H₀) (h1332 : Stmt13_3_2)
    (hC : Concl T L V H₀) {N R : Subgroup G} (hNH : N ≤ H₀)
    (hHN : H₀ ≤ Subgroup.normalizer (N : Set G)) (hRH : R ≤ H₀)
    (hRn : H₀ ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 ↥R)
    (h3 : ∀ n ∈ N, ∃ k : ℕ, n ^ 3 ^ k ∈ R) : N ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRO : R ≤ pCoreOf 2 H₀ := le_pCoreOf_of_le_normalizer 2 hRH hRn hR2
  have hOT : pCoreOf 2 H₀ ≤ T := pCoreOf_le_of_le S₀.hyp (le_sup_right.trans S₀.hz.1.1)
  have hLM := l1T_le_M S₀.hyp h1332
  have hNn : (modO2Image H₀ N).Normal := by
    have hn : (N.subgroupOf H₀).Normal := by
      refine ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (hHN g.2) n).mp (Subgroup.mem_subgroupOf.mp hn)
      simpa using h1
    exact hn.map _ (QuotientGroup.mk'_surjective _)
  have hN3 : IsPGroup 3 ↥(modO2Image H₀ N) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := mem_modO2Image'.mp hy
    obtain ⟨k, hk⟩ := h3 n hn
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : n ^ 3 ^ k ∈ CFSG.pCore 2 ↥H₀ := by
      rw [← mem_pCoreOf_iff]
      simpa using hRO hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr h1
  have hNP : modO2Image H₀ N ≤ CFSG.pCore 3 (↥H₀ ⧸ CFSG.pCore 2 ↥H₀) := le_sSup ⟨hNn, hN3⟩
  intro n hn
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) ⟨n, hNH hn⟩ ∈
      CFSG.pCore 3 (↥H₀ ⧸ CFSG.pCore 2 ↥H₀) :=
    hNP ⟨⟨n, hNH hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
  rcases hC with h | h
  · rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← mem_pCoreOf_iff] at hmem
    exact le_sup_right.trans hLM (hOT hmem)
  · rw [h] at hmem
    obtain ⟨a, ha, hae⟩ := mem_modO2Image'.mp hmem
    have h1 : a⁻¹ * ⟨n, hNH hn⟩ ∈ CFSG.pCore 2 ↥H₀ := by
      rw [← QuotientGroup.eq]
      exact hae
    rw [← mem_pCoreOf_iff] at h1
    have e : n = (a : G) * ((a⁻¹ * ⟨n, hNH hn⟩ : ↥H₀) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ (le_sup_left.trans hLM ha) (le_sup_right.trans hLM (hOT h1))

end CFSG.Quasithin.H13.L32A.R727

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Four

open Subgroup

variable {G : Type} [Group G] [Finite G]

private lemma conj_mem_centralizer {M V : Subgroup G} (hMV : M ≤ normalizer (V : Set G))
    {m y : G} (hm : m ∈ M) (hy : y ∈ centralizer (V : Set G)) :
    m * y * m⁻¹ ∈ centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro v hv
  have hvn : m⁻¹ * v * m ∈ V := (Subgroup.mem_set_normalizer_iff''.mp (hMV hm) v).mp hv
  calc v * (m * y * m⁻¹) = m * ((m⁻¹ * v * m) * y) * m⁻¹ := by group
    _ = m * (y * (m⁻¹ * v * m)) * m⁻¹ := by rw [hy (m⁻¹ * v * m) hvn]
    _ = (m * y * m⁻¹) * v := by group

private lemma le_normalizer_inf_centralizer {M V : Subgroup G}
    (hMV : M ≤ normalizer (V : Set G)) :
    M ≤ normalizer ((M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨mul_mem (mul_mem hm hy.1) (M.inv_mem hm), conj_mem_centralizer hMV hm hy.2⟩
  · rintro x hx
    refine ⟨m⁻¹ * x * m, ⟨?_, ?_⟩, ?_⟩
    · exact mul_mem (mul_mem (M.inv_mem hm) hx.1) hm
    · simpa using conj_mem_centralizer hMV (M.inv_mem hm) hx.2
    · rw [MulAut.conj_apply]; group

private lemma forall_pow_mem_iff_exists_index_pow {C K : Subgroup G} (hCK : C ≤ K)
    (hKn : (C.subgroupOf K).Normal) :
    (∀ y : K, ∃ k : ℕ, (y ^ 2 ^ k : K) ∈ C.subgroupOf K) ↔
      ∃ n : ℕ, (C.subgroupOf K).index = 2 ^ n := by
  haveI : (C.subgroupOf K).Normal := hKn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    have hP : IsPGroup 2 (↥K ⧸ C.subgroupOf K) := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf K) q
      obtain ⟨k, hk⟩ := h y
      refine ⟨k, ?_⟩
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (N := C.subgroupOf K) (y ^ 2 ^ k)).mpr hk
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    exact ⟨n, by rw [Subgroup.index_eq_card]; exact hn⟩
  · rintro ⟨n, hn⟩
    have hcard : Nat.card (↥K ⧸ C.subgroupOf K) = 2 ^ n := by
      rw [← Subgroup.index_eq_card]; exact hn
    have hP : IsPGroup 2 (↥K ⧸ C.subgroupOf K) := IsPGroup.of_card hcard
    intro y
    obtain ⟨k, hk⟩ := hP (QuotientGroup.mk' (C.subgroupOf K) y)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (C.subgroupOf K)) (y ^ 2 ^ k) = 1
    rw [map_pow, hk]

private lemma iSup_conj_zpowers_eq_closure (M : Subgroup G) (v : G) :
    (⨆ m : M, (zpowers v).map (MulAut.conj (m : G)).toMonoidHom) =
      closure {x : G | ∃ m ∈ M, x = m * v * m⁻¹} := by
  apply le_antisymm
  · refine iSup_le fun m => ?_
    rw [MonoidHom.map_zpowers]
    refine Subgroup.zpowers_le.mpr ?_
    exact Subgroup.subset_closure ⟨(m : G), m.2, rfl⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨m, hm, rfl⟩
    exact Subgroup.mem_iSup_of_mem (⟨m, hm⟩ : M)
      (by simpa [MulAut.conj_apply] using Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers v))

private lemma centralizer_conj_iff (M : Subgroup G) {z : G} :
    (∀ g : G, g ∉ M → ¬ centralizer ({z} : Set G) ≤ CFSG.Open.uniqueFourConj g M) ↔
      (∀ g : G, g ∉ M → ¬ centralizer ({z} : Set G) ≤ M.map (MulAut.conj g).toMonoidHom) := by
  constructor
  · intro h g hg
    have hg' : g⁻¹ ∉ M := fun hmem => hg (inv_mem_iff.mp hmem)
    simpa [CFSG.Open.uniqueFourConj] using h g⁻¹ hg'
  · intro h g hg
    have hg' : g⁻¹ ∉ M := fun hmem => hg (inv_mem_iff.mp hmem)
    simpa [CFSG.Open.uniqueFourConj] using h g⁻¹ hg'

theorem inCalV_iff (M V : Subgroup G) :
    CFSG.Yardstones.Mf4cdcdf2e013.InCalV M V ↔ UC22.InCalV M V := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h3, h4, h2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h4, h2, h3⟩

theorem oTwoQuotTrivial_iff_twoReduced {M V : Subgroup G} (hMV : M ≤ normalizer (V : Set G)) :
    CFSG.Yardstones.Mf4cdcdf2e013.OTwoQuotTrivial M (M ⊓ centralizer (V : Set G)) ↔
      UC22.TwoReduced M V := by
  set C : Subgroup G := M ⊓ centralizer (V : Set G) with hC
  have hCnorm : M ≤ normalizer (C : Set G) := by
    rw [hC]; exact le_normalizer_inf_centralizer hMV
  have hCsub : ∀ {K : Subgroup G}, C ≤ K → K ≤ M → (C.subgroupOf K).Normal := by
    intro K hCK hKM
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hCK).mpr (hKM.trans hCnorm)
  have hsub : ∀ {K : Subgroup G}, K ≤ M →
      (centralizer (V : Set G)).subgroupOf K = C.subgroupOf K := by
    intro K hKM
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf]
    exact ⟨fun h => ⟨hKM x.2, h⟩, fun h => h.2⟩
  constructor
  · intro hOT K hKM hKN hCK hindex
    have hKn := hCsub hCK hKM
    obtain ⟨n, hn⟩ := hindex
    rw [hsub hKM] at hn
    have hpow' : ∀ y : K, ∃ k : ℕ, (y ^ 2 ^ k : K) ∈ C.subgroupOf K :=
      (forall_pow_mem_iff_exists_index_pow hCK hKn).mpr ⟨n, hn⟩
    have hpow : ∀ x ∈ K, ∃ k : ℕ, x ^ (2 ^ k) ∈ C := by
      intro x hx
      obtain ⟨k, hk⟩ := hpow' ⟨x, hx⟩
      exact ⟨k, Subgroup.mem_subgroupOf.mp hk⟩
    have hKC : K = C := hOT K hCK hKM hKN hpow
    rw [hKC, hC]
    exact inf_le_right
  · intro hTR N hCN hNM hNN hpow
    have hNn := hCsub hCN hNM
    have hpow' : ∀ y : N, ∃ k : ℕ, (y ^ 2 ^ k : N) ∈ C.subgroupOf N := by
      intro y
      obtain ⟨k, hk⟩ := hpow y y.2
      exact ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩
    have hindex : ∃ n : ℕ, (C.subgroupOf N).index = 2 ^ n :=
      (forall_pow_mem_iff_exists_index_pow hCN hNn).mp hpow'
    have hcent : N ≤ centralizer (V : Set G) := by
      refine hTR N hNM hNN hCN ?_
      obtain ⟨n, hn⟩ := hindex
      exact ⟨n, by rw [hsub hNM]; exact hn⟩
    exact le_antisymm (by rw [hC]; exact le_inf hNM hcent) hCN

theorem inCalV1_iff {M : Subgroup G} (hM : CFSG.Open.uniqueFourIsMaxTwoLocal M)
    (T V : Subgroup G) :
    CFSG.Yardstones.Mf4cdcdf2e013.InCalV1 M T V ↔ UC22.InCalV1 M T V := by
  rw [CFSG.Yardstones.Mf4cdcdf2e013.InCalV1, UC22.InCalV1]
  refine and_congr (inCalV_iff M V) ?_
  constructor
  · intro h
    rw [UC22.UniqueMax, UC22.calMOf]
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hN, hXN⟩
      exact h N hN hXN
    · rintro rfl
      exact ⟨hM, inf_le_left⟩
  · intro h N hN hXN
    have hNmem : N ∈ UC22.calMOf
        (M ⊓ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) :=
      ⟨hN, hXN⟩
    rw [h] at hNmem
    simpa using hNmem

theorem inCalW_iff {M : Subgroup G} (hM : CFSG.Open.uniqueFourIsMaxTwoLocal M)
    (T V : Subgroup G) :
    CFSG.Yardstones.Mf4cdcdf2e013.InCalW M T V ↔ UC22.InCalW M T V := by
  constructor
  · intro h
    have hMV : M ≤ normalizer (V : Set G) := h.1.1.2.2.2
    exact ⟨(inCalV1_iff hM T V).mp h.1, h.2.1, (oTwoQuotTrivial_iff_twoReduced hMV).mp h.2.2⟩
  · intro h
    have hMV : M ≤ normalizer (V : Set G) := h.1.1.2.2.1
    exact ⟨(inCalV1_iff hM T V).mpr h.1, h.2.1, (oTwoQuotTrivial_iff_twoReduced hMV).mpr h.2.2⟩

theorem inCalWStar_iff {M : Subgroup G} (hM : CFSG.Open.uniqueFourIsMaxTwoLocal M)
    (T V : Subgroup G) :
    CFSG.Yardstones.Mf4cdcdf2e013.InCalWStar M T V ↔ UC22.InCalWStar M T V := by
  rw [CFSG.Yardstones.Mf4cdcdf2e013.InCalWStar, UC22.InCalWStar]
  refine and_congr (inCalW_iff hM T V) ?_
  constructor <;> intro h W hW hWV
  · exact h W ((inCalW_iff hM T W).mpr hW) hWV
  · exact h W ((inCalW_iff hM T W).mp hW) hWV

theorem inCalV0_iff (M V₀ V : Subgroup G) :
    CFSG.Yardstones.Mf4cdcdf2e013.InCalV0 M V₀ V ↔ UC22.InCalV0 M V₀ V := by
  have hgen : (∀ v ∈ V, v ∉ V₀ →
        (⨆ m : M, (zpowers v).map (MulAut.conj (m : G)).toMonoidHom) = V) ↔
      (∀ v ∈ V, v ∉ V₀ → closure {x : G | ∃ m ∈ M, x = m * v * m⁻¹} = V) := by
    refine forall_congr' fun v => ?_
    rw [iSup_conj_zpowers_eq_closure M v]
  rw [CFSG.Yardstones.Mf4cdcdf2e013.InCalV0, UC22.InCalV0]
  constructor
  · rintro ⟨hA, hB, hC, hD, hE, hF, hG⟩
    have hMV : M ≤ normalizer (V : Set G) := hB.2.2.2
    exact ⟨(inCalV_iff M V₀).mp hA, (inCalV_iff M V).mp hB, hC, hD, hE, hgen.mp hF,
      (not_congr (oTwoQuotTrivial_iff_twoReduced hMV)).mp hG⟩
  · rintro ⟨hA, hB, hC, hD, hE, hF, hG⟩
    have hMV : M ≤ normalizer (V : Set G) := hB.2.2.1
    exact ⟨(inCalV_iff M V₀).mpr hA, (inCalV_iff M V).mpr hB, hC, hD, hE, hgen.mpr hF,
      (not_congr (oTwoQuotTrivial_iff_twoReduced hMV)).mpr hG⟩

theorem hyp122_iff {M : Subgroup G} (hM : CFSG.Open.uniqueFourIsMaxTwoLocal M)
    (T V₀ V : Subgroup G) :
    CFSG.Yardstones.Mf4cdcdf2e013.Hyp122 M T V₀ V ↔
      UC22.InCalV0 M V₀ V ∧ UC22.CentralizersUnique M T ∧ ∀ W : Subgroup G, ¬ UC22.InCalW M T W := by
  rw [CFSG.Yardstones.Mf4cdcdf2e013.Hyp122]
  refine and_congr (inCalV0_iff M V₀ V)
    (and_congr ?_ (forall_congr' fun W => not_congr (inCalW_iff hM T W)))
  rw [UC22.CentralizersUnique]
  refine forall_congr' fun z => forall_congr' fun _ => ?_
  refine imp_congr_right fun _ => imp_congr_right fun _ => ?_
  exact and_congr Iff.rfl (centralizer_conj_iff M)

theorem hyp123_iff {M : Subgroup G} (hM : CFSG.Open.uniqueFourIsMaxTwoLocal M)
    (T V₀ V : Subgroup G) :
    CFSG.Yardstones.Mf4cdcdf2e013.Hyp123 M T V₀ V ↔ UC22.Hyp123 M T V₀ V := by
  rw [CFSG.Yardstones.Mf4cdcdf2e013.Hyp123, UC22.Hyp123]
  exact or_congr (and_congr (inCalWStar_iff hM T V) Iff.rfl) (hyp122_iff hM T V₀ V)

theorem centralizesQuot_iff {V₀ V : Subgroup G} (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {t : G}
    (ht : ∀ v ∈ V, t * v * t⁻¹ ∈ V) :
    CFSG.Yardstones.Mf4cdcdf2e013.CentralizesQuot V₀ V t ↔ UC22.CentralizesMod V₀ V t := by
  rw [CFSG.Yardstones.Mf4cdcdf2e013.CentralizesQuot, UC22.CentralizesMod]
  constructor
  · intro h v hv
    have hcomm := hV v⁻¹ (inv_mem hv) (t * v * t⁻¹) (ht v hv)
    rw [← hcomm]
    exact h v hv
  · intro h v hv
    have hcomm := hV v⁻¹ (inv_mem hv) (t * v * t⁻¹) (ht v hv)
    rw [hcomm]
    exact h v hv

theorem minCodimGt_of_mBarGT {M V₀ V : Subgroup G} (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hMV : M ≤ normalizer (V : Set G)) {n : ℕ} (h : UC22.MBarGT M V₀ V n) :
    CFSG.Yardstones.Mf4cdcdf2e013.MinCodimGt M V₀ V n := by
  constructor
  · intro t ht hnt hntt
    have htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V := fun v hv =>
      (Subgroup.mem_set_normalizer_iff.mp (hMV ht) v).mp hv
    have htV2 : ∀ v ∈ V, (t * t) * v * (t * t)⁻¹ ∈ V := by
      intro v hv
      convert htV (t * v * t⁻¹) (htV v hv) using 1
      group
    have h1 : 2 ^ (n + 1) * Nat.card (UC22.centMod V₀ V t) ≤ Nat.card V :=
      h.1 t ht (fun hc => hnt ((centralizesQuot_iff hV htV).mpr hc))
        ((centralizesQuot_iff hV htV2).mp hntt)
    have hiff : ∀ v : G, (v ∈ V ∧ v⁻¹ * (t * v * t⁻¹) ∈ V₀) ↔
        (v ∈ V ∧ t * v * t⁻¹ * v⁻¹ ∈ V₀) := by
      intro v
      constructor
      · rintro ⟨hv, hmem⟩
        exact ⟨hv, by rwa [hV v⁻¹ (inv_mem hv) (t * v * t⁻¹) (htV v hv)] at hmem⟩
      · rintro ⟨hv, hmem⟩
        exact ⟨hv, by rwa [← hV v⁻¹ (inv_mem hv) (t * v * t⁻¹) (htV v hv)] at hmem⟩
    have hcard : Nat.card {v : G // v ∈ V ∧ v⁻¹ * (t * v * t⁻¹) ∈ V₀} =
        Nat.card (UC22.centMod V₀ V t) :=
      Nat.card_congr (Equiv.subtypeEquivRight hiff)
    rw [hcard]
    exact h1
  · intro hquot
    apply h.2
    intro t ht ht2
    have htV : ∀ v ∈ V, t * v * t⁻¹ ∈ V := fun v hv =>
      (Subgroup.mem_set_normalizer_iff.mp (hMV ht) v).mp hv
    have htV2 : ∀ v ∈ V, (t * t) * v * (t * t)⁻¹ ∈ V := by
      intro v hv
      convert htV (t * v * t⁻¹) (htV v hv) using 1
      group
    exact (centralizesQuot_iff hV htV).mp
      (hquot t ht ((centralizesQuot_iff hV htV2).mpr ht2))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Four

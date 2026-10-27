module

public import CFSG.Quasithin.H13.NQCatUniqueModels
public import CFSG.Quasithin.H13.NQBlockOriginalSupplements

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_comm_of_decomposition {E O P T : Subgroup G}
    (hTE : T ≤ normalizer (E : Set G)) (hOT : O ≤ T)
    (h₁ : ∀ y ∈ E, ∃ o ∈ O, ∃ a ∈ P, y = o * a) (h₂ : ∀ y ∈ E, ∃ a ∈ P, ∃ o ∈ O, y = a * o)
    (hPE : P ≤ E) : (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G) := by
  ext x
  simp only [Set.mem_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, t, ht, rfl⟩
    have hy : t⁻¹ * a * t ∈ E := by
      have := (mem_normalizer_iff.mp (hTE (T.inv_mem ht)) a).mp (hPE ha)
      simpa using this
    obtain ⟨o, ho, a', ha', hdec⟩ := h₁ _ hy
    refine ⟨t * o, T.mul_mem ht (hOT ho), a', ha', ?_⟩
    calc t * o * a' = t * (o * a') := mul_assoc _ _ _
      _ = t * (t⁻¹ * a * t) := by rw [hdec]
      _ = a * t := by group
  · rintro ⟨t, ht, a, ha, rfl⟩
    have hy : t * a * t⁻¹ ∈ E := (mem_normalizer_iff.mp (hTE ht) a).mp (hPE ha)
    obtain ⟨a', ha', o, ho, hdec⟩ := h₂ _ hy
    refine ⟨a', ha', o * t, T.mul_mem (hOT ho) ht, ?_⟩
    calc a' * (o * t) = a' * o * t := (mul_assoc _ _ _).symm
      _ = t * a * t⁻¹ * t := by rw [hdec]
      _ = t * a := by group

theorem nq_original_configuration_has_another_maximal_two_local
    (h3 : ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
      fusionIsBenderGroup G ∨ UniqueSmallModel G)
    {T L M : Subgroup G} (h : QTNQ T L M) :
    ∃ H₀ : Subgroup G, quasithinIsMaxTwoLocal H₀ ∧ T ≤ H₀ ∧ H₀ ≠ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  by_contra hno
  have huniq : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → T ≤ M' → M' = M := by
    intro M' hM' hTM'
    by_contra hne
    exact hno ⟨M', hM', hTM', hne⟩
  have hTs : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, h.sylow.1, ?_⟩
    have hidx : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    rw [hidx]
    exact h.sylow.2
  have hset : UniqueSetting G T M :=
    { simple := h.simple
      nonabelian := h.nonabelian
      qtke := qtkeCore_of_cat h.nonabelian h.qtke
      sylow := hTs
      maxLocal := h.max_two_local
      le := h.t_le
      unique := huniq }
  have hmodel := h3 G T M hset
  obtain ⟨p, hp, hp5, D, -, hDp, hDshape, hwit⟩ :=
    NQBlock.nq_characteristic_radical_odd_residual_witness
      (NQBlock.isStronglyQuasithin_L_of_qtnq h) (NQSetup.isCComponent_top_of_qtnq h)
      h.not_quasisimple
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  set N : Subgroup ↥L := CFSG.pCore 2 ↥L with hN
  set π : ↥L →* ↥L ⧸ N := QuotientGroup.mk' N with hπ
  set E : Subgroup ↥L := D.comap π with hE
  obtain ⟨hEc, -⟩ := hwit E _ rfl rfl
  have hDpg : IsPGroup p ↥D := (CFSG.pCore_isPGroup).to_le hDp
  have hDnc : ¬ IsCyclic ↥D := by
    rcases hDshape with ⟨hDe, hD2⟩ | ⟨hDna, -, -⟩
    · have := hDe
      exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hD2
    · intro hcyc
      exact hDna (@IsCyclic.isMulCommutative _ _ hcyc)
  have hNc : N.Characteristic := by
    rw [hN]
    infer_instance
  have hNE : N ≤ E := fun x hx => by
    show π x ∈ D
    have h1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact D.one_mem
  obtain ⟨P₀⟩ : Nonempty (Sylow p ↥E) := inferInstance
  let φ : ↥E →* ↥D := (π.comp E.subtype).codRestrict D fun e => e.2
  have hφ : Function.Surjective φ := by
    rintro ⟨d, hd⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N d
    exact ⟨⟨x, hd⟩, rfl⟩
  have hPtop : ((P₀.mapSurjective hφ : Sylow p ↥D) : Subgroup ↥D) = ⊤ :=
    ((P₀.mapSurjective hφ).is_maximal' (hDpg.to_subgroup ⊤) le_top).symm
  have hdecL : ∀ e ∈ E, ∃ a ∈ (P₀ : Subgroup ↥E).map E.subtype, a⁻¹ * e ∈ N := by
    intro e he
    have hmem : φ ⟨e, he⟩ ∈ (P₀ : Subgroup ↥E).map φ := by
      rw [← Sylow.coe_mapSurjective hφ, hPtop]
      exact mem_top _
    obtain ⟨a, ha, hae⟩ := hmem
    refine ⟨(a : ↥L), ⟨a, ha, rfl⟩, ?_⟩
    have h1 : π (a : ↥L) = π e := congrArg Subtype.val hae
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change (π (a : ↥L))⁻¹ * π e = 1
    rw [h1, inv_mul_cancel]
  set EG : Subgroup G := E.map L.subtype with hEG
  set OG : Subgroup G := N.map L.subtype with hOG
  set P : Subgroup G := ((P₀ : Subgroup ↥E).map E.subtype).map L.subtype with hPdef
  have hTL : T ≤ normalizer (L : Set G) := h.eq_normalizer ▸ h.t_le
  have hTE : T ≤ normalizer (EG : Set G) := fun t ht =>
    LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic E (hTL ht)
  have hOT : OG ≤ T := by
    have hMsyl : IsSylowIn 2 T M :=
      ⟨h.t_le, h.sylow.1, fun hd => h.sylow.2 (hd.trans (Subgroup.relIndex_dvd_index_of_le h.t_le))⟩
    have hOM : OG ≤ M := (map_subtype_le _).trans h.l_le
    have hMN : M ≤ normalizer (OG : Set G) := fun m hm =>
      LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic N (h.eq_normalizer ▸ hm)
    exact hMsyl.le_of_normal hOM ((normal_subgroupOf_iff_le_normalizer hOM).mpr hMN)
      (CFSG.pCore_isPGroup.map _)
  have hPE : P ≤ EG := map_mono (map_subtype_le _)
  have hNn : ∀ (x : ↥L), ∀ n ∈ N, x * n * x⁻¹ ∈ N := fun x n hn =>
    (CFSG.pCore_normal (p := 2) (G := ↥L)).conj_mem n hn x
  have h₂ : ∀ y ∈ EG, ∃ a ∈ P, ∃ o ∈ OG, y = a * o := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨a, ha, han⟩ := hdecL e he
    refine ⟨(a : G), ⟨a, ha, rfl⟩, ((a⁻¹ * e : ↥L) : G), ⟨_, han, rfl⟩, ?_⟩
    simp
  have h₁ : ∀ y ∈ EG, ∃ o ∈ OG, ∃ a ∈ P, y = o * a := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨a, ha, han⟩ := hdecL e he
    refine ⟨((e * a⁻¹ : ↥L) : G), ⟨e * a⁻¹, ?_, rfl⟩, (a : G), ⟨a, ha, rfl⟩, ?_⟩
    · have := hNn a _ han
      simpa [mul_assoc] using this
    · simp
  have hPT := mul_comm_of_decomposition hTE hOT h₁ h₂ hPE
  have hPp : IsPGroup p P := (P₀.isPGroup'.map E.subtype).map L.subtype
  set TS : Sylow 2 G := h.sylow.1.toSylow h.sylow.2 with hTS
  have hTSc : (TS : Subgroup G) = T := IsPGroup.toSylow_coe h.sylow.1 h.sylow.2
  have hcyc := NQCat.exact_uniqueness_models_have_cyclic_large_prime_sylow_products G
    h.nonabelian hmodel TS hp hp5 P hPp hPT
  apply hDnc
  have hsurj : Function.Surjective ((φ.comp (P₀ : Subgroup ↥E).subtype)) := by
    intro d
    have hd : d ∈ (P₀ : Subgroup ↥E).map φ := by
      rw [← Sylow.coe_mapSurjective hφ, hPtop]
      exact mem_top d
    obtain ⟨a, ha, rfl⟩ := hd
    exact ⟨⟨a, ha⟩, rfl⟩
  have hP₀P : ↥(P₀ : Subgroup ↥E) ≃* ↥P :=
    ((P₀ : Subgroup ↥E).equivMapOfInjective E.subtype E.subtype_injective).trans
      (((P₀ : Subgroup ↥E).map E.subtype).equivMapOfInjective L.subtype L.subtype_injective)
  have : IsCyclic ↥(P₀ : Subgroup ↥E) := isCyclic_of_surjective hP₀P.symm.toMonoidHom
    hP₀P.symm.surjective
  exact isCyclic_of_surjective _ hsurj

end CFSG.Quasithin.H13.NQCore

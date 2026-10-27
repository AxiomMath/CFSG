module

public import CFSG.Quasithin.H13.NQBlockOriginalRadical
public import CFSG.Quasithin.SteinbergCDSupplementCentralizerCore

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped Pointwise

theorem pCore_eq_bot_of_simple_nonabelian {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    {p : ℕ} [Fact p.Prime] (hnab : ∃ a b : Q, a * b ≠ b * a) : CFSG.pCore p Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore p Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hP : IsPGroup p Q := by
      have h1 := CFSG.pCore_isPGroup (p := p) (G := Q)
      rw [h] at h1
      exact IsPGroup.of_equiv h1 Subgroup.topEquiv
    have : Nontrivial Q := ⟨⟨a * b, b * a, hab⟩⟩
    have hZ := hP.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Q) with hc | hc
    · exact (nontrivial_iff_ne_bot _).mp hZ hc
    · have ha : a ∈ center Q := hc ▸ mem_top a
      exact hab (mem_center_iff.mp ha b).symm

theorem radical_centralizer_eq_two_core {B : Type*} [Group B] [Finite B] (L : Subgroup B)
    [L.Normal] (T : Sylow 2 B) (hBLT : L ⊔ (T : Subgroup B) = ⊤)
    (hsimple : IsSimpleGroup (L ⧸ CFSG.solvableRadical L))
    (hnab : ∃ a b : L ⧸ CFSG.solvableRadical L, a * b ≠ b * a)
    (N C R A K : Subgroup B) (hN : N = (CFSG.solvableRadical L).map L.subtype)
    (hC : ∀ b : B, b ∈ C ↔ ∀ x ∈ L, x⁻¹ * (b * x * b⁻¹) ∈ N)
    (hR : R = (T : Subgroup B) ⊓ C) (hA : A = L ⊓ normalizer (R : Set B))
    (hK : K = (CFSG.perfectResidual A).map A.subtype) :
    R = inSubgroup (CFSG.pCore 2) (K ⊔ (T : Subgroup B)) ∧
      R = inSubgroup (CFSG.pCore 2) (normalizer (R : Set B)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, h6, -, h8, h9, h10, -, -, -, h14, h15, -, -, -, -, h20⟩ :=
    radical_Sylow_normalizer_perfect_residual_supplement L T hBLT hsimple hnab N C R A K hN hC hR
      hA hK
  have hNn : N.Normal := by
    rw [hN]
    refine ⟨fun n hn g => ?_⟩
    have hchar := (CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L).1
    have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.solvableRadical L) (show g ∈ normalizer (L : Set B) by
        rw [normalizer_eq_top_iff.mpr inferInstance]
        exact mem_top g)
    exact (mem_normalizer_iff.mp h1 n).mp hn
  have hNL : N ≤ L := hN ▸ map_subtype_le _
  have hNsub : N.subgroupOf L = CFSG.solvableRadical L := by
    rw [hN]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hcore : CFSG.pCore 2 (L ⧸ N.subgroupOf L) = ⊥ := by
    let e : (L ⧸ N.subgroupOf L) ≃* (L ⧸ CFSG.solvableRadical L) :=
      QuotientGroup.quotientMulEquivOfEq hNsub
    have h1 := CFSG.LieType.SteinbergBR.pCore_map_equiv 2 e
    rw [pCore_eq_bot_of_simple_nonabelian hnab] at h1
    exact (map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hsec : centralizerSection (T : Subgroup B) L N = R := by
    ext m
    rw [mem_centralizerSection_iff_of_le hNL, hR, mem_inf, hC]
    refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h x hx => ?_⟩
    · have h1 := h x⁻¹ (inv_mem hx)
      rwa [show x⁻¹ * m * x⁻¹⁻¹ * m⁻¹ = x⁻¹ * (m * x * m⁻¹) by group] at h1
    · have h1 := h x⁻¹ (inv_mem hx)
      rwa [show x⁻¹⁻¹ * (m * x⁻¹ * m⁻¹) = x * m * x⁻¹ * m⁻¹ by group] at h1
  have hTR : (T : Subgroup B) ≤ normalizer (R : Set B) := h6 ▸ le_sup_right
  have hAR : A ≤ normalizer (R : Set B) := hA ▸ inf_le_right
  have hKL : K ≤ L := by
    rw [hK]
    exact (map_subtype_le _).trans (hA ▸ inf_le_left)
  have hTK : (T : Subgroup B) ≤ normalizer (K : Set B) :=
    hTR.trans ((normal_subgroupOf_iff_le_normalizer h14).mp h15)
  have hLNK : (L : Set B) = (N : Set B) * (K : Set B) := by
    rw [h10]
    exact normal_mul N K
  have hRK : ((centralizerSection (T : Subgroup B) L N).subgroupOf (K ⊔ (T : Subgroup B))).Normal :=
    hsec ▸ h20
  have e1 := (SteinbergCD.prime_core_free_quotient_supplement_centralizer_is_prime_core
    Nat.prime_two hcore T hKL hTK hLNK hRK).2
  have hAL : A ≤ L := hA ▸ inf_le_left
  have hTA : (T : Subgroup B) ≤ normalizer (A : Set B) :=
    hTR.trans ((normal_subgroupOf_iff_le_normalizer hAR).mp h8)
  have hLNA : (L : Set B) = (N : Set B) * (A : Set B) := by
    rw [h9]
    exact normal_mul N A
  have hRA :
      ((centralizerSection (T : Subgroup B) L N).subgroupOf (A ⊔ (T : Subgroup B))).Normal := by
    rw [hsec, ← h6]
    infer_instance
  have e2 := (SteinbergCD.prime_core_free_quotient_supplement_centralizer_is_prime_core
    Nat.prime_two hcore T hAL hTA hLNA hRA).2
  rw [hsec, ← h6] at e2
  rw [hsec] at e1
  exact ⟨e1, e2⟩

section Setting

variable {G : Type} [Group G]

theorem original_subgroupOf_normal {T L : Subgroup G} (hTL : T ≤ normalizer (L : Set G)) :
    (L.subgroupOf (L ⊔ T)).Normal :=
  (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hTL)

theorem original_subgroupOf_sup_eq_top (T L : Subgroup G) :
    L.subgroupOf (L ⊔ T) ⊔ T.subgroupOf (L ⊔ T) = ⊤ := by
  apply map_injective (L ⊔ T).subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
    map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]

theorem original_simple [Finite G] {T L : Subgroup G} (hLc : L ∈ cComp (L ⊔ T)) :
    IsSimpleGroup (L.subgroupOf (L ⊔ T) ⧸ CFSG.solvableRadical (L.subgroupOf (L ⊔ T))) ∧
      ∃ a b : L.subgroupOf (L ⊔ T) ⧸ CFSG.solvableRadical (L.subgroupOf (L ⊔ T)),
        a * b ≠ b * a := by
  have hLc' : L.subgroupOf (L ⊔ T) ∈ cComp (⊤ : Subgroup ↥(L ⊔ T)) := subgroupOf_mem_cComp hLc
  have h1 := subgroupOf_mem_cComp (cComp_mem_of_le hLc' le_rfl le_top)
  rw [subgroupOf_self] at h1
  exact simple_radical_quotient_of_isCComponent_top (mem_cComp_top_iff_isCComponent.mp h1)

theorem original_R_map {T L R : Subgroup G} (hR : (R : Set G) = nqOriginalCentralizer T L)
    {T' C' : Subgroup ↥(L ⊔ T)} (hT' : T' = T.subgroupOf (L ⊔ T))
    (hC' : ∀ b, b ∈ C' ↔ ∀ x ∈ L.subgroupOf (L ⊔ T), x⁻¹ * (b * x * b⁻¹) ∈
      (CFSG.solvableRadical (L.subgroupOf (L ⊔ T))).map (L.subgroupOf (L ⊔ T)).subtype) :
    (T' ⊓ C').map (L ⊔ T).subtype = R := by
  have hLB : L ≤ L ⊔ T := le_sup_left
  have hTB : T ≤ L ⊔ T := le_sup_right
  have hNmap := map_radical_subgroupOf hLB
  have hNL : ∀ l ∈ L, ∀ n ∈ (CFSG.solvableRadical L).map L.subtype,
      l * n * l⁻¹ ∈ (CFSG.solvableRadical L).map L.subtype := by
    rintro l hl _ ⟨n, hn, rfl⟩
    have hn' : (⟨l, hl⟩ : L) * n * (⟨l, hl⟩ : L)⁻¹ ∈ CFSG.solvableRadical L :=
      CFSG.ABGLocalTools.solvableRadical_normal.conj_mem n hn ⟨l, hl⟩
    exact ⟨_, hn', rfl⟩
  have hmem : ∀ y, y ∈ R ↔ y ∈ nqOriginalCentralizer T L := fun y => by
    rw [← hR]
    rfl
  ext x
  rw [hmem]
  constructor
  · rintro ⟨b, ⟨hbT, hbC⟩, rfl⟩
    rw [hT'] at hbT
    refine ⟨hbT, fun l hl => ?_⟩
    have h := (hC' b).mp hbC ⟨l, hLB hl⟩ hl
    have h' : l⁻¹ * ((b : G) * l * (b : G)⁻¹) ∈ (CFSG.solvableRadical L).map L.subtype := by
      rw [← hNmap]
      exact ⟨_, h, rfl⟩
    have h'' := hNL l hl _ h'
    rwa [show l * (l⁻¹ * ((b : G) * l * (b : G)⁻¹)) * l⁻¹ = (b : G) * l * (b : G)⁻¹ * l⁻¹ by
      group] at h''
  · rintro ⟨hxT, hx⟩
    refine ⟨⟨x, hTB hxT⟩, ⟨?_, ?_⟩, rfl⟩
    · rw [hT']
      exact hxT
    · refine (hC' _).mpr ?_
      rintro ⟨y, hyB⟩ hy
      have hyL : y ∈ L := hy
      have h2 : y⁻¹ * (x * y * x⁻¹) ∈ (CFSG.solvableRadical L).map L.subtype := by
        have h3 := hNL y⁻¹ (inv_mem hyL) _ (hx y hyL)
        rwa [show y⁻¹ * (x * y * x⁻¹ * y⁻¹) * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹) by group] at h3
      rw [← hNmap] at h2
      obtain ⟨z, hz, hzeq⟩ := h2
      have hz' : z = (⟨y, hyB⟩ : (L ⊔ T : Subgroup G))⁻¹ * (⟨x, hTB hxT⟩ * ⟨y, hyB⟩ *
          (⟨x, hTB hxT⟩ : (L ⊔ T : Subgroup G))⁻¹) := Subtype.ext hzeq
      rw [← hz']
      exact hz

theorem original_A_map {T L R : Subgroup G} {R' : Subgroup ↥(L ⊔ T)}
    (hR' : R'.map (L ⊔ T).subtype = R) :
    (L.subgroupOf (L ⊔ T) ⊓ normalizer (R' : Set ↥(L ⊔ T))).map (L ⊔ T).subtype =
      L ⊓ normalizer (R : Set G) := by
  rw [map_inf_eq _ _ _ (L ⊔ T).subtype_injective, map_subtype_normalizer_eq, hR',
    map_subgroupOf_eq_of_le le_sup_left, ← inf_assoc, inf_eq_left.mpr (le_sup_left : L ≤ L ⊔ T)]

theorem original_K_map [Finite G] {T L R : Subgroup G}
    (hR : (R : Set G) = nqOriginalCentralizer T L) {R' : Subgroup ↥(L ⊔ T)}
    (hR' : R'.map (L ⊔ T).subtype = R) :
    ((CFSG.perfectResidual ↥(L.subgroupOf (L ⊔ T) ⊓ normalizer (R' : Set ↥(L ⊔ T)))).map
      (L.subgroupOf (L ⊔ T) ⊓ normalizer (R' : Set ↥(L ⊔ T))).subtype).map (L ⊔ T).subtype =
        nqOriginalK T L := by
  rw [← perfectCore_eq_map_perfectResidual, map_perfectCore, original_A_map hR',
    perfectCore_eq_map_perfectResidual]
  unfold nqOriginalK
  rw [hR]

theorem map_inSubgroup_pCore {B : Subgroup G} (X : Subgroup B) (p : ℕ) :
    (inSubgroup (CFSG.pCore p) X).map B.subtype = pCoreOf p (X.map B.subtype) := by
  let e : X ≃* (X.map B.subtype) := X.equivMapOfInjective B.subtype B.subtype_injective
  have he : (X.map B.subtype).subtype.comp e.toMonoidHom = B.subtype.comp X.subtype := by
    ext
    rfl
  unfold inSubgroup pCoreOf
  rw [Subgroup.map_map, ← he, ← Subgroup.map_map,
    CFSG.LieType.SteinbergBR.pCore_map_equiv]

end Setting

variable {G : Type} [Group G] [Finite G]

theorem original_radical_normalizer_centralizer_is_two_core {T L M : Subgroup G}
    (h : QTNQ T L M) {R : Subgroup G} (hR : (R : Set G) = nqOriginalCentralizer T L) :
    R = pCoreOf 2 (nqOriginalK T L ⊔ T) ∧ R = pCoreOf 2 ((L ⊔ T) ⊓ normalizer (R : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : T ≤ normalizer (L : Set G) := h.eq_normalizer ▸ h.t_le
  have hL'n := original_subgroupOf_normal hTL
  have hT2 : IsPGroup 2 (T.subgroupOf (L ⊔ T)) := h.sylow.1.comap_subtype
  let T' : Sylow 2 ↥(L ⊔ T) := hT2.toSylow h.maximal_local.1.2.2.1
  have hT' : (T' : Subgroup ↥(L ⊔ T)) = T.subgroupOf (L ⊔ T) := IsPGroup.toSylow_coe _ _
  have hBLT : L.subgroupOf (L ⊔ T) ⊔ (T' : Subgroup ↥(L ⊔ T)) = ⊤ :=
    hT' ▸ original_subgroupOf_sup_eq_top T L
  obtain ⟨hsimple, hnab⟩ := original_simple h.maximal_local.1.2.1
  obtain ⟨C', hC'⟩ := exists_quotientCentralizer (L.subgroupOf (L ⊔ T))
    ((CFSG.solvableRadical (L.subgroupOf (L ⊔ T))).map (L.subgroupOf (L ⊔ T)).subtype)
  have hRmap := original_R_map hR hT' hC'
  obtain ⟨h1, h2⟩ := radical_centralizer_eq_two_core (L.subgroupOf (L ⊔ T)) T' hBLT hsimple hnab
    _ C' _ _ _ rfl hC' rfl rfl rfl
  have hKmap := original_K_map hR hRmap
  have hT'map : (T' : Subgroup ↥(L ⊔ T)).map (L ⊔ T).subtype = T := by
    rw [hT', map_subgroupOf_eq_of_le le_sup_right]
  have e1 := congrArg (Subgroup.map (L ⊔ T).subtype) h1
  rw [hRmap, map_inSubgroup_pCore, Subgroup.map_sup, hKmap, hT'map] at e1
  have e2 := congrArg (Subgroup.map (L ⊔ T).subtype) h2
  rw [map_inSubgroup_pCore, map_subtype_normalizer_eq, hRmap] at e2
  exact ⟨e1, e2⟩

end CFSG.Quasithin.H13.NQBlock

module

public import CFSG.Quasithin.H13.NQBlockCentralCoreOffender
public import CFSG.Quasithin.H13.NQTermPrimeResidualDefs
public import CFSG.Quasithin.H13.NQBlockRadicalSylow
public import CFSG.Quasithin.H13.NQBlockResidualBar
public import CFSG.Quasithin.H13.NQBlockResidualSupplement
public import CFSG.Quasithin.SteinbergCCPrimeWitness

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped commutatorElement

section Transport

variable {G : Type*} [Group G]

theorem exists_quotientCentralizer {B : Type*} [Group B] (L N : Subgroup B) [hL : L.Normal] :
    ∃ C : Subgroup B, ∀ b : B, b ∈ C ↔ ∀ x ∈ L, x⁻¹ * (b * x * b⁻¹) ∈ N := by
  refine ⟨{ carrier := {b | ∀ x ∈ L, x⁻¹ * (b * x * b⁻¹) ∈ N}
            one_mem' := by
              intro x _
              rw [one_mul, inv_one, mul_one, inv_mul_cancel]
              exact one_mem N
            mul_mem' := by
              intro a b ha hb x hx
              have e : x⁻¹ * (a * b * x * (a * b)⁻¹) = (x⁻¹ * (b * x * b⁻¹)) *
                  ((b * x * b⁻¹)⁻¹ * (a * (b * x * b⁻¹) * a⁻¹)) := by group
              rw [e]
              exact mul_mem (hb x hx) (ha _ (hL.conj_mem x hx b))
            inv_mem' := by
              intro a ha x hx
              have h1 := ha _ (hL.conj_mem x hx a⁻¹)
              have e : x⁻¹ * (a⁻¹ * x * a⁻¹⁻¹) =
                  ((a⁻¹ * x * a⁻¹⁻¹)⁻¹ * (a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹))⁻¹ := by group
              rw [e]
              exact inv_mem h1 }, fun _ => Iff.rfl⟩

theorem map_subtype_normalizer_eq (B : Subgroup G) (X : Subgroup B) :
    (normalizer (X : Set B)).map B.subtype =
      B ⊓ normalizer ((X.map B.subtype : Subgroup G) : Set G) := by
  have hX : (X.map B.subtype).subgroupOf B = X :=
    comap_map_eq_self_of_injective B.subtype_injective X
  have h := subgroupOf_normalizer_eq (map_subtype_le X)
  rw [hX] at h
  rw [← h, subgroupOf_map_subtype, inf_comm]

theorem map_radical_subgroupOf {L B : Subgroup G} (hLB : L ≤ B) :
    ((CFSG.solvableRadical (L.subgroupOf B)).map (L.subgroupOf B).subtype).map B.subtype =
      (CFSG.solvableRadical L).map L.subtype := by
  let e : L.subgroupOf B ≃* L := subgroupOfEquivOfLe hLB
  have he : B.subtype.comp (L.subgroupOf B).subtype = L.subtype.comp e.toMonoidHom := by
    ext
    rfl
  rw [Subgroup.map_map, he, ← Subgroup.map_map,
    CFSG.LieType.SteinbergBR.solvableRadical_map_equiv]

theorem map_subtype_mem_cComp_of_mem [Finite G] {B : Subgroup G} {K X : Subgroup B}
    (h : K ∈ cComp X) : K.map B.subtype ∈ cComp (X.map B.subtype) := by
  have hKX : K ≤ X := le_of_mem_cComp h
  let e : X ≃* (X.map B.subtype) := X.equivMapOfInjective B.subtype B.subtype_injective
  have h1 := cComp_map_mulEquiv e (subgroupOf_mem_cComp h)
  rw [map_top_of_surjective _ e.surjective] at h1
  have h2 := map_subtype_mem_cComp h1
  have h3 : ((K.subgroupOf X).map e.toMonoidHom).map (X.map B.subtype).subtype =
      K.map B.subtype := by
    rw [Subgroup.map_map]
    have he : (X.map B.subtype).subtype.comp e.toMonoidHom = B.subtype.comp X.subtype := by
      ext
      rfl
    rw [he, ← Subgroup.map_map, map_subgroupOf_eq_of_le hKX]
  rwa [h3] at h2

theorem le_pCoreOf_of_subgroupOf_normal {p : ℕ} {X R : Subgroup G} (hRX : R ≤ X)
    (hn : (R.subgroupOf X).Normal) (hR : IsPGroup p R) : R ≤ pCoreOf p X := by
  have h1 : R.subgroupOf X ≤ CFSG.Open.pCore p X := by
    exact SteinbergCC.le_pCore_of_normal_of_isPGroup hn hR.comap_subtype
  have h2 := map_mono (f := X.subtype) h1
  rwa [map_subgroupOf_eq_of_le hRX] at h2

theorem exists_maxTwoLocal_ge_of_isTwoLocal [Finite G] {H : Subgroup G} (hH : IsTwoLocal H) :
    ∃ M : Subgroup G, quasithinIsMaxTwoLocal M ∧ H ≤ M := by
  obtain ⟨M, hHM, hM⟩ := Finite.exists_le_maximal (p := IsTwoLocal) hH
  exact ⟨M, ⟨hM.1, fun K hK hMK => le_antisymm (hM.2 hK hMK) hMK⟩, hHM⟩

end Transport

variable {G : Type} [Group G] [Finite G]

theorem exists_originalCentralizer {T L : Subgroup G} (hTL : T ≤ normalizer (L : Set G)) :
    ∃ R : Subgroup G, (R : Set G) = nqOriginalCentralizer T L := by
  have hchar := (CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization L).1
  have hTN : ∀ t ∈ T, ∀ n ∈ (CFSG.solvableRadical L).map L.subtype,
      t * n * t⁻¹ ∈ (CFSG.solvableRadical L).map L.subtype := fun t ht n hn =>
    (mem_normalizer_iff.mp (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.solvableRadical L) (hTL ht)) n).mp hn
  refine ⟨{ carrier := nqOriginalCentralizer T L
            one_mem' := ⟨one_mem T, fun l _ => by
              rw [one_mul, inv_one, mul_one, mul_inv_cancel]
              exact one_mem _⟩
            mul_mem' := by
              rintro s t ⟨hs, hs'⟩ ⟨ht, ht'⟩
              refine ⟨mul_mem hs ht, fun l hl => ?_⟩
              have e : s * t * l * (s * t)⁻¹ * l⁻¹ =
                  s * (t * l * t⁻¹ * l⁻¹) * s⁻¹ * (s * l * s⁻¹ * l⁻¹) := by group
              rw [e]
              exact mul_mem (hTN s hs _ (ht' l hl)) (hs' l hl)
            inv_mem' := by
              rintro t ⟨ht, ht'⟩
              refine ⟨inv_mem ht, fun l hl => ?_⟩
              have hl' : t⁻¹ * l * t ∈ L := by
                have h1 := (mem_normalizer_iff.mp (hTL (inv_mem ht)) l).mp hl
                rwa [inv_inv] at h1
              have e : t⁻¹ * l * t⁻¹⁻¹ * l⁻¹ =
                  (t * (t⁻¹ * l * t) * t⁻¹ * (t⁻¹ * l * t)⁻¹)⁻¹ := by group
              rw [e]
              exact inv_mem (ht' _ hl') }, rfl⟩

theorem original_radical_supplement {T L : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTs : ¬ 2 ∣ (T.subgroupOf (L ⊔ T)).index) (hTL : T ≤ normalizer (L : Set G))
    (hLc : L ∈ cComp (L ⊔ T)) {R : Subgroup G} (hR : (R : Set G) = nqOriginalCentralizer T L) :
    R ≤ T ∧ T ≤ normalizer (R : Set G) ∧ pCoreOf 2 (L ⊔ T) ≤ R ∧
      (L ⊔ T) ⊓ normalizer (R : Set G) = (L ⊓ normalizer (R : Set G)) ⊔ T ∧
      L = (CFSG.solvableRadical L).map L.subtype ⊔ (L ⊓ normalizer (R : Set G)) ∧
      L = (CFSG.solvableRadical L).map L.subtype ⊔ nqOriginalK T L ∧
      nqOriginalK T L ≠ ⊥ ∧ ⁅nqOriginalK T L, nqOriginalK T L⁆ = nqOriginalK T L ∧
      nqOriginalK T L ≤ normalizer (R : Set G) ∧ T ≤ normalizer (nqOriginalK T L : Set G) ∧
      nqOriginalK T L ∈ cComp (nqOriginalK T L ⊔ T) ∧ R ≤ nqOriginalK T L ⊔ T ∧
      (R.subgroupOf (nqOriginalK T L ⊔ T)).Normal := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLB : L ≤ L ⊔ T := le_sup_left
  have hTB : T ≤ L ⊔ T := le_sup_right
  have hBL : L ⊔ T ≤ normalizer (L : Set G) := sup_le le_normalizer hTL
  have hL'n : (L.subgroupOf (L ⊔ T)).Normal := (normal_subgroupOf_iff_le_normalizer hLB).mpr hBL
  have hT2' : IsPGroup 2 (T.subgroupOf (L ⊔ T)) := hT2.comap_subtype
  let T' : Sylow 2 ↥(L ⊔ T) := hT2'.toSylow hTs
  have hT'eq : (T' : Subgroup ↥(L ⊔ T)) = T.subgroupOf (L ⊔ T) := IsPGroup.toSylow_coe _ _
  have hT'map : (T' : Subgroup ↥(L ⊔ T)).map (L ⊔ T).subtype = T := by
    rw [hT'eq, map_subgroupOf_eq_of_le hTB]
  have hBLT : L.subgroupOf (L ⊔ T) ⊔ (T' : Subgroup ↥(L ⊔ T)) = ⊤ := by
    apply map_injective (L ⊔ T).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLB, hT'map, ← MonoidHom.range_eq_map,
      range_subtype]
  have hLc' : L.subgroupOf (L ⊔ T) ∈ cComp (⊤ : Subgroup ↥(L ⊔ T)) := subgroupOf_mem_cComp hLc
  have hLtop : CFSG.IsCComponent (⊤ : Subgroup (L.subgroupOf (L ⊔ T))) := by
    have h1 := subgroupOf_mem_cComp (cComp_mem_of_le hLc' le_rfl le_top)
    rw [subgroupOf_self] at h1
    exact mem_cComp_top_iff_isCComponent.mp h1
  obtain ⟨hsimple, hnab⟩ := simple_radical_quotient_of_isCComponent_top hLtop
  set L' := L.subgroupOf (L ⊔ T) with hL'
  set N' := (CFSG.solvableRadical L').map L'.subtype with hN'
  obtain ⟨C', hC'⟩ := exists_quotientCentralizer L' N'
  set R' := (T' : Subgroup ↥(L ⊔ T)) ⊓ C' with hR'
  set A' := L' ⊓ normalizer (R' : Set ↥(L ⊔ T)) with hA'
  set K' := (CFSG.perfectResidual A').map A'.subtype with hK'
  obtain ⟨-, -, -, -, h5, h6, -, -, h9, h10, h11, h12, -, h14, h15, -, -, h18, h19, h20⟩ :=
    radical_Sylow_normalizer_perfect_residual_supplement L' T' hBLT hsimple hnab N' C' R' A' K'
      rfl hC' rfl rfl rfl
  have hNmap : N'.map (L ⊔ T).subtype = (CFSG.solvableRadical L).map L.subtype :=
    map_radical_subgroupOf hLB
  have hNL : ∀ l ∈ L, ∀ n ∈ (CFSG.solvableRadical L).map L.subtype,
      l * n * l⁻¹ ∈ (CFSG.solvableRadical L).map L.subtype := by
    rintro l hl _ ⟨n, hn, rfl⟩
    have hn' : (⟨l, hl⟩ : L) * n * (⟨l, hl⟩ : L)⁻¹ ∈ CFSG.solvableRadical L :=
      CFSG.ABGLocalTools.solvableRadical_normal.conj_mem n hn ⟨l, hl⟩
    exact ⟨_, hn', rfl⟩
  have hmem : ∀ y, y ∈ R ↔ y ∈ nqOriginalCentralizer T L := fun y => by
    rw [← hR]
    rfl
  have hRmap : R'.map (L ⊔ T).subtype = R := by
    ext x
    rw [hmem]
    constructor
    · rintro ⟨b, ⟨hbT, hbC⟩, rfl⟩
      rw [hT'eq] at hbT
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
      · rw [hT'eq]
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
  have hNRmap : (normalizer (R' : Set ↥(L ⊔ T))).map (L ⊔ T).subtype =
      (L ⊔ T) ⊓ normalizer (R : Set G) := by
    rw [map_subtype_normalizer_eq, hRmap]
  have hAmap : A'.map (L ⊔ T).subtype = L ⊓ normalizer (R : Set G) := by
    rw [hA', map_inf_eq _ _ _ (L ⊔ T).subtype_injective, hNRmap, map_subgroupOf_eq_of_le hLB,
      ← inf_assoc, inf_eq_left.mpr hLB]
  have hKmap : K'.map (L ⊔ T).subtype = nqOriginalK T L := by
    rw [hK', ← perfectCore_eq_map_perfectResidual, map_perfectCore, hAmap,
      perfectCore_eq_map_perfectResidual]
    unfold nqOriginalK
    rw [hR]
  have hKTmap : (K' ⊔ (T' : Subgroup ↥(L ⊔ T))).map (L ⊔ T).subtype = nqOriginalK T L ⊔ T := by
    rw [Subgroup.map_sup, hKmap, hT'map]
  have hNR : (L ⊔ T) ⊓ normalizer (R : Set G) ≤ normalizer (R : Set G) := inf_le_right
  have hTR' : (T' : Subgroup ↥(L ⊔ T)) ≤ normalizer (R' : Set ↥(L ⊔ T)) := h6 ▸ le_sup_right
  have hTR : T ≤ normalizer (R : Set G) := by
    have h := map_mono (f := (L ⊔ T).subtype) hTR'
    rw [hT'map, hNRmap] at h
    exact h.trans hNR
  have hRT : R ≤ T := fun x hx => ((hmem x).mp hx).1
  have hpcore : pCoreOf 2 (L ⊔ T) ≤ R := by
    have h := map_mono (f := (L ⊔ T).subtype) h5
    rw [hRmap] at h
    exact h
  have hNB : (L ⊔ T) ⊓ normalizer (R : Set G) = (L ⊓ normalizer (R : Set G)) ⊔ T := by
    rw [← hNRmap, h6, Subgroup.map_sup, hAmap, hT'map]
  have hLNA : L = (CFSG.solvableRadical L).map L.subtype ⊔ (L ⊓ normalizer (R : Set G)) := by
    have h := congrArg (Subgroup.map (L ⊔ T).subtype) h9
    rwa [map_subgroupOf_eq_of_le hLB, Subgroup.map_sup, hNmap, hAmap] at h
  have hLNK : L = (CFSG.solvableRadical L).map L.subtype ⊔ nqOriginalK T L := by
    have h := congrArg (Subgroup.map (L ⊔ T).subtype) h10
    rwa [map_subgroupOf_eq_of_le hLB, Subgroup.map_sup, hNmap, hKmap] at h
  have hKne : nqOriginalK T L ≠ ⊥ := by
    rw [← hKmap]
    exact fun h => h11 ((map_eq_bot_iff_of_injective _ (L ⊔ T).subtype_injective).mp h)
  have hKperf : ⁅nqOriginalK T L, nqOriginalK T L⁆ = nqOriginalK T L := by
    rw [← hKmap, ← map_commutator, h12]
  have hKR : nqOriginalK T L ≤ normalizer (R : Set G) := by
    have h := map_mono (f := (L ⊔ T).subtype) h14
    rw [hKmap, hNRmap] at h
    exact h.trans hNR
  have hTK : T ≤ normalizer (nqOriginalK T L : Set G) := by
    have h1 : normalizer (R' : Set ↥(L ⊔ T)) ≤ normalizer (K' : Set ↥(L ⊔ T)) :=
      (normal_subgroupOf_iff_le_normalizer h14).mp h15
    have h := map_mono (f := (L ⊔ T).subtype) (hTR'.trans h1)
    rw [hT'map, map_subtype_normalizer_eq, hKmap] at h
    exact h.trans inf_le_right
  have hKc : nqOriginalK T L ∈ cComp (nqOriginalK T L ⊔ T) := by
    have h1 := map_subtype_mem_cComp (mem_cComp_top_iff_isCComponent.mpr h18)
    rw [map_subgroupOf_eq_of_le le_sup_left] at h1
    have h2 := map_subtype_mem_cComp_of_mem h1
    rwa [hKmap, hKTmap] at h2
  have hRKT : R ≤ nqOriginalK T L ⊔ T := by
    have h := map_mono (f := (L ⊔ T).subtype) h19
    rwa [hRmap, hKTmap] at h
  have hRn : (R.subgroupOf (nqOriginalK T L ⊔ T)).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hRKT).mpr ?_
    have h := map_mono (f := (L ⊔ T).subtype) ((normal_subgroupOf_iff_le_normalizer h19).mp h20)
    rw [hKTmap, hNRmap] at h
    exact h.trans hNR
  exact ⟨hRT, hTR, hpcore, hNB, hLNA, hLNK, hKne, hKperf, hKR, hTK, hKc, hRKT, hRn⟩

theorem original_radical_normalizer_local_and_Thompson_failure {T L M : Subgroup G}
    (h : QTNQ T L M) {R : Subgroup G} (hR : (R : Set G) = nqOriginalCentralizer T L) :
    R ≠ ⊥ ∧ L = (CFSG.solvableRadical L).map L.subtype ⊔ (L ⊓ normalizer (R : Set G)) ∧
      L = (CFSG.solvableRadical L).map L.subtype ⊔ nqOriginalK T L ∧
      R ≤ nqOriginalK T L ⊔ T ∧ (R.subgroupOf (nqOriginalK T L ⊔ T)).Normal ∧
      quasithinIsLocal T (nqOriginalK T L) ∧ nqOriginalK T L ⊔ T ≤ normalizer (R : Set G) ∧
      (⁅L, (CFSG.elemThompson T 2).map T.subtype⁆ ≠ L →
        (CFSG.elemThompson T 2).map T.subtype ≤ R ∧
        (CFSG.elemThompson R 2).map R.subtype = (CFSG.elemThompson T 2).map T.subtype ∧
        (CFSG.elemThompson T 2).map T.subtype ≠ ⊥ ∧
        nqOriginalK T L ⊔ T ≤ normalizer ((CFSG.elemThompson T 2).map T.subtype : Set G) ∧
        (quasithinIsMaxTwoLocal M ∧ nqOriginalK T L ⊔ T ≤ M ∧
            (∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → nqOriginalK T L ⊔ T ≤ M' →
              M' = M) →
          normalizer ((CFSG.elemThompson T 2).map T.subtype : Set G) ≤ M)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hTL : T ≤ normalizer (L : Set G) := h.eq_normalizer ▸ h.t_le
  have hLc : L ∈ cComp (L ⊔ T) := h.maximal_local.1.2.1
  obtain ⟨hRT, hTR, hpcore, -, hLNA, hLNK, -, -, hKR, -, hKc, hRKT, hRn⟩ :=
    original_radical_supplement hT2 h.maximal_local.1.2.2.1 hTL hLc hR
  have hRne : R ≠ ⊥ := fun hR0 => h.maximal_local.1.2.2.2 (le_bot_iff.mp (hR0 ▸ hpcore))
  have hR2 : IsPGroup 2 R := hT2.to_le hRT
  have hKTR : nqOriginalK T L ⊔ T ≤ normalizer (R : Set G) := sup_le hKR hTR
  have hloc : quasithinIsLocal T (nqOriginalK T L) := by
    refine ⟨hT2, hKc, fun h2 => h.sylow.2 (h2.trans (relIndex_dvd_index_of_le le_sup_right)),
      fun h0 => hRne (le_bot_iff.mp ?_)⟩
    rw [← h0]
    exact le_pCoreOf_of_subgroupOf_normal hRKT hRn hR2
  refine ⟨hRne, hLNA, hLNK, hRKT, hRn, hloc, hKTR, fun hLJ => ?_⟩
  have hJT : (CFSG.elemThompson T 2).map T.subtype ≤ T := map_subtype_le _
  have hDL : ⁅L, (CFSG.elemThompson T 2).map T.subtype⁆ ≤ L := by
    rw [commutator_le]
    intro l hl j hj
    have hjl : j * l⁻¹ * j⁻¹ ∈ L := (mem_normalizer_iff.mp (hTL (hJT hj)) l⁻¹).mp (inv_mem hl)
    rw [commutatorElement_def, show l * j * l⁻¹ * j⁻¹ = l * (j * l⁻¹ * j⁻¹) by group]
    exact mul_mem hl hjl
  have hDn : L ≤ normalizer ((⁅L, (CFSG.elemThompson T 2).map T.subtype⁆ : Subgroup G) : Set G) :=
    fun z hz => mem_normalizer_of_conj_mem
      (fun c hc => SteinbergCC.conj_mem_commutator_left hz hc)
      (fun c hc => by simpa using SteinbergCC.conj_mem_commutator_left (inv_mem hz) hc)
  have hDN : ⁅L, (CFSG.elemThompson T 2).map T.subtype⁆ ≤
      (CFSG.solvableRadical L).map L.subtype := by
    rw [← solvRad_eq_map_solvableRadical]
    exact le_solvRad_of_subnormal_lt hLc
      (A3.subnormal_of_normal hDL ((normal_subgroupOf_iff_le_normalizer hDL).mpr hDn))
      (lt_of_le_of_ne hDL hLJ)
  have hJR : (CFSG.elemThompson T 2).map T.subtype ≤ R := by
    intro j hj
    rw [← SetLike.mem_coe, hR]
    refine ⟨hJT hj, fun l hl => ?_⟩
    have hc : ⁅j, l⁆ ∈ ⁅L, (CFSG.elemThompson T 2).map T.subtype⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator hj hl
    rw [commutatorElement_def] at hc
    exact hDN hc
  have hJeq : (CFSG.elemThompson R 2).map R.subtype = (CFSG.elemThompson T 2).map T.subtype :=
    SteinbergBQ.map_elemThompson_subtype_eq_of_le hRT hJR
  have hJne : (CFSG.elemThompson T 2).map T.subtype ≠ ⊥ := by
    have : Nontrivial T := (nontrivial_iff_ne_bot T).mpr fun hT0 =>
      hRne (le_bot_iff.mp (hT0 ▸ hRT))
    exact fun h0 => elemThompson_ne_bot_of_isPGroup hT2
      ((map_eq_bot_iff_of_injective _ T.subtype_injective).mp h0)
  have hKTJ : nqOriginalK T L ⊔ T ≤
      normalizer ((CFSG.elemThompson T 2).map T.subtype : Set G) := by
    have : (CFSG.elemThompson R 2).Characteristic := BlueprintB2.elemThompson_characteristic _ 2
    rw [← hJeq]
    exact hKTR.trans (LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  refine ⟨hJR, hJeq, hJne, hKTJ, ?_⟩
  rintro ⟨-, -, huniq⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge_of_isTwoLocal
    ⟨(CFSG.elemThompson T 2).map T.subtype, hJne, hT2.to_le hJT, rfl⟩
  rw [← huniq M' hM' (hKTJ.trans hle)]
  exact hle

end CFSG.Quasithin.H13.NQBlock

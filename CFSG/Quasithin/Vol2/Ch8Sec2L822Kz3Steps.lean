module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Steps1
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3List
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3LzCore
public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bSmall

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs CFSG.Quasithin
  CFSG.Quasithin.H13.L319 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.EmptyFaithfulMultiple
open scoped IsMulCommutative

theorem pCoreOf_le_pCoreOf_kz3 {G : Type} [Group G] {Gz K : Subgroup G} (hKG : K ≤ Gz)
    (hKn : Gz ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 Gz :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKG)
    (fun g hg => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hKn hg))
    (kzIsPGroupPCoreOf_kz3 K)

theorem pCoreOf_inf_le_pCoreOf_kz3 {G : Type} [Group G] {Gz K : Subgroup G} (hKG : K ≤ Gz)
    (hKn : Gz ≤ Subgroup.normalizer (K : Set G)) :
    CFSG.Open.pCoreOf 2 Gz ⊓ K ≤ CFSG.Open.pCoreOf 2 K := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    (IsPGroup.to_le (kzIsPGroupPCoreOf_kz3 Gz) inf_le_left)
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have h1 := Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Gz (Subgroup.le_normalizer (hKG hk))) h
  have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hk) h
  exact and_congr h1 h2

@[expose] noncomputable def kzIncl_kz3 {G : Type} [Group G] {Gz K : Subgroup G} (hKG : K ≤ Gz)
    (hKn : Gz ≤ Subgroup.normalizer (K : Set G)) :
    (↥K ⧸ CFSG.pCore 2 ↥K) →* (↥Gz ⧸ CFSG.pCore 2 ↥Gz) :=
  QuotientGroup.map (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥Gz) (Subgroup.inclusion hKG) (by
    intro x hx
    rw [Subgroup.mem_comap, mem_pCore_iff_kz2]
    rw [mem_pCore_iff_kz2] at hx
    exact pCoreOf_le_pCoreOf_kz3 hKG hKn hx)

theorem kzIncl_injective_kz3 {G : Type} [Group G] {Gz K : Subgroup G} (hKG : K ≤ Gz)
    (hKn : Gz ≤ Subgroup.normalizer (K : Set G)) : Function.Injective (kzIncl_kz3 hKG hKn) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  have h1 : (QuotientGroup.mk (Subgroup.inclusion hKG x) : ↥Gz ⧸ CFSG.pCore 2 ↥Gz) = 1 := ha
  rw [QuotientGroup.eq_one_iff, mem_pCore_iff_kz2] at h1
  rw [QuotientGroup.eq_one_iff, mem_pCore_iff_kz2]
  exact pCoreOf_inf_le_pCoreOf_kz3 hKG hKn ⟨h1, x.2⟩

theorem kzIncl_map_modO2Image_kz3 {G : Type} [Group G] {Gz K Lz : Subgroup G} (hKG : K ≤ Gz)
    (hKn : Gz ≤ Subgroup.normalizer (K : Set G)) (hLK : Lz ≤ K) :
    (modO2Image K Lz).map (kzIncl_kz3 hKG hKn) = modO2Image Gz Lz := by
  unfold modO2Image
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥Gz))
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hw))
  · intro hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥K) ⟨(g : G), hLK (Subgroup.mem_subgroupOf.mp hg)⟩,
      Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
        (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hg)), rfl⟩

theorem kzBq_card_kz3 {G : Type} [Group G] {Gz K Lz : Subgroup G} (hKG : K ≤ Gz)
    (hKn : Gz ≤ Subgroup.normalizer (K : Set G)) (hLK : Lz ≤ K)
    (hcard : Nat.card ↥(modO2Image Gz Lz) = 69120) : Nat.card ↥(modO2Image K Lz) = 69120 := by
  have h : Nat.card ↥((modO2Image K Lz).map (kzIncl_kz3 hKG hKn)) = Nat.card ↥(modO2Image K Lz) :=
    Subgroup.card_map_of_injective (kzIncl_injective_kz3 hKG hKn)
  rw [kzIncl_map_modO2Image_kz3 hKG hKn hLK] at h
  rw [← h]
  exact hcard

theorem kzBq_commutator_kz3 {G : Type} [Group G] {K Lz : Subgroup G} (hLK : Lz ≤ K)
    (hLzP : ⁅Lz, Lz⁆ = Lz) :
    ⁅modO2Image K Lz, modO2Image K Lz⁆ = modO2Image K Lz := by
  have hA : ⁅Lz.subgroupOf K, Lz.subgroupOf K⁆ = Lz.subgroupOf K :=
    perfect_comap_subtype_kz3 hLK hLzP
  unfold modO2Image
  rw [← Subgroup.map_commutator, hA]

theorem kzBq_invariant_kz3 {G : Type} [Group G] {K Lz T : Subgroup G}
    (hLzT : T ≤ Subgroup.normalizer (Lz : Set G)) {t : G} (htT : t ∈ T)
    (htN : t ∈ Subgroup.normalizer (K : Set G)) {x : ↥K ⧸ CFSG.pCore 2 ↥K}
    (hx : x ∈ modO2Image K Lz) : kzQmap_kz2 K t htN x ∈ modO2Image K Lz := by
  unfold modO2Image at hx ⊢
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
  change kzQmap_kz2 K t htN (QuotientGroup.mk w) ∈ _
  rw [kzQmap_mk_kz2]
  have hc : kzConjK_kz2 K t htN w ∈ Lz.subgroupOf K := by
    rw [Subgroup.mem_subgroupOf, kzConjK_val_kz2]
    exact (Subgroup.mem_normalizer_iff.mp (hLzT htT) (w : G)).mp (Subgroup.mem_subgroupOf.mp hw)
  exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) hc

theorem kzStepsRel_kz3_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : CFSG.QuasithinUnique.Vol2Native.A312ForSQTKCat) (hAut : KzAutE9Perfect_kz3)
    (h3228 : Stmt3_2_2_eight) :
    ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
      Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I → Row711M22Code T L I →
        ¬ autOn T (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I) →
        ∀ H : Subgroup G, IsHStar T (fsuM T L) H → fsuV T I ≤ pCoreOf 2 H → IsXi T (twoResidual H) →
          (pCoreOf 2 (twoResidual H)).relIndex (twoResidual H) = 9 →
          ∀ (z : G) (P Lz : Subgroup G), z ≠ 1 → z ∈ fsuV T I → z ∈ quasithinOmegaOneCenter T →
            H ≤ Subgroup.centralizer ({z} : Set G) → T ≤ Subgroup.centralizer ({z} : Set G) →
            P ≤ twoResidual H → IsPGroup 3 P → Nat.card P = 9 →
            Kz134Concl_kz (Subgroup.centralizer ({z} : Set G)) T (twoResidual H) P →
            Lz ≤ Subgroup.centralizer ({z} : Set G) → T ≤ Subgroup.normalizer (Lz : Set G) →
            Lz ∈ lFamily T →
            (NoThreeInCV (fsuM T L) (fsuV T I) → IsAlt 6 (↥Lz ⧸ CFSG.pCore 2 ↥Lz)) →
            (¬ NoThreeInCV (fsuM T L) (fsuV T I) →
              IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6))) →
            ∃ K : Subgroup G, K ≤ Subgroup.centralizer ({z} : Set G) ∧
              T ≤ Subgroup.normalizer (K : Set G) ∧ twoResidual H ≤ K ∧
              (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
               ∃ Bq : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K),
                 Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) ∧
                 Nat.card Bq = 69120 ∧ ⁅Bq, Bq⁆ = Bq ∧
                 ∀ t ∈ T, ∀ ht : t ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ Bq, kzQmap_kz2 K t ht x ∈ Bq) := by
  intro G _ _ T L I hyp h731 h821 hc hrow hrowM hnot H hH hVH hXi hrel z P Lz hz1 hzV hzΩ hHz hTz
    hPX hP3 hPcard hcon hLzG hLzT hLzF hA6 hH6
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, -⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hz2 : z ^ 2 = 1 := hV.2 z hzV
  have hLzq : CFSG.Quasithin.IsAlt 6 (↥Lz ⧸ CFSG.pCore 2 ↥Lz) ∨
      CFSG.Quasithin.IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6)) := by
    by_cases hN : NoThreeInCV (fsuM T L) (fsuV T I)
    · exact Or.inl (hA6 hN)
    · exact Or.inr (hH6 hN)
  obtain ⟨K, hK, hLK, hXK, hTK, hKq, htail⟩ :=
    kz3_steps12 hyp h37 h38 h39 hAut hXi hrel hz1 hz2 hHz hTz hPX hP3 hPcard hcon hLzG hLzT hLzF hLzq
  have hKG : K ≤ Subgroup.centralizer ({z} : Set G) := le_of_mem_cComp hK
  have hTsyl : IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTz
  have hpC : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ :=
    kzPCoreCentralizerNeBot_kz3 hz1 hz2
  have hKn : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mp
      (lemma_1_2_4_normal hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 hpC hTsyl hLzF hLK hK hLzT)
  have hLzP : ⁅Lz, Lz⁆ = Lz := perfect_of_mem_cComp (X := Lz ⊔ T) hLzF
  have hloc : LocalSQTK G := by
    haveI : IsSimpleGroup G := hyp.fsu.simple
    exact (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hM11 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) = 7920 :=
    CFSG.Sporadic.Mathieu.card_M11
  have hHe : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) = 4030387200 :=
    CFSG.Sporadic.He.card_He
  have hM23 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M23) = 10200960 :=
    CFSG.OddStandard.Solomon75.card_nativeM23
  have hM24 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) = 244823040 :=
    CFSG.Sporadic.Mathieu.card_M24
  have hJ4 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J4) = 86775571046077562880 :=
    CFSG.Sporadic.J4.card_J4
  rcases kz3_list_match hloc h312 hTsyl hpC hLzG hLzF hLzP hLzq hK hLK hTK hKq htail
      hM11 hHe hM23 hM24 hJ4 with hM | ⟨hHe', hcard⟩
  · exact ⟨K, hKG, hTK, hXK, Or.inl hM⟩
  · refine ⟨K, hKG, hTK, hXK, Or.inr ⟨modO2Image K Lz, hHe', ?_, kzBq_commutator_kz3 hLK hLzP, ?_⟩⟩
    · exact kzBq_card_kz3 hKG hKn hLK hcard
    · intro t htT htN x hx
      exact kzBq_invariant_kz3 hLzT htT htN hx

end CFSG.Quasithin.H13

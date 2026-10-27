module

public import CFSG.Quasithin.Vol2.Ch12Sec6L26i
public import CFSG.Quasithin.Vol2.Ch12Sec6L26j
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom CFSG.SectionRank
open CFSG.Blueprint CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F Equiv

namespace S126L26

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCore_two_iff {H : Subgroup G} (y : ↥H) :
    y ∈ CFSG.pCore 2 ↥H ↔ (y : G) ∈ pCoreOf 2 H := (CFSG.mem_openPCoreOf_iff y).symm

omit [Finite G] in
theorem mk_eq_one_iff {H : Subgroup G} (y : ↥H) :
    (y : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 ↔ (y : G) ∈ pCoreOf 2 H :=
  (QuotientGroup.eq_one_iff y).trans (mem_pCore_two_iff y)

omit [Finite G] in
theorem mk_comm_iff {H : Subgroup G} (a b : ↥H) :
    (a : ↥H ⧸ CFSG.pCore 2 ↥H) * b = b * a ↔
      (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∈ pCoreOf 2 H := by
  have e : ((a * b * a⁻¹ * b⁻¹ : ↥H) : G) = (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ := rfl
  rw [← e, ← mk_eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv]
  constructor
  · intro h
    rw [h]
    group
  · intro h
    calc (a : ↥H ⧸ CFSG.pCore 2 ↥H) * b =
        (a : ↥H ⧸ CFSG.pCore 2 ↥H) * b * (a : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ *
          (b : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ * (b * a) := by group
      _ = b * a := by rw [h, one_mul]

omit [Finite G] in
theorem isSylowTwoOf_mk {H S : Subgroup G} (hS : IsSylowTwoOf S H) :
    IsSylowTwoOf ((S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) ⊤ := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨le_top, hS2.map _, ?_⟩
  rw [show (((S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).subgroupOf ⊤).index =
    ((S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).index from
      Subgroup.relIndex_top_right _]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _))

variable {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem exists_component (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24)
    (h38 : Vol2Native.A38ForSQTKCat) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G} (hHz : S126.InHz T L F.V1 H)
    {v : G} (hv : v ∈ V) (hvH : v ∈ H) (hvQ : v ∉ pCoreOf 2 H) :
    ∃ K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), CFSG.IsComponent K ∧
      ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ Subgroup.normalizer (K : Set _) ∧
      ∃ k ∈ K, ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) * k ≠
        k * ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) := by
  classical
  have hyp := hH.hyp
  have : IsSimpleGroup G := hyp.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat hyp.nonabelian hyp.qtke).1
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hHz.1.2
  obtain ⟨h, hidx, -, -, -⟩ := setup126 h1224 F hH hZ hHz
  have hTH : T ≤ H := le_sup_right.trans hHz.1.1
  have hVT : V ≤ T := h.V_le_T
  have hT5 : T ≤ Subgroup.normalizer (F.V5 : Set G) := le_sup_right.trans h.L₁T_normalizes_Vp
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := fun t ht => h.normalizer_le ⟨hTH ht, hT5 ht⟩
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_le h.sylow hTH
  have hvp : v ∉ F.V5 := fun h5 => hvQ (h.Vp_le_pCoreOf_and_commutator_le.1 h5)
  have hV : ¬ V ≤ pCoreOf 2 H := fun hle => hvQ (hle hv)
  refine S126C.exists_component hQ.o2 (h38 _ hQ) (isSylowTwoOf_mk hTs) ⟨⟨v, hvH⟩, ?_, rfl⟩
    ?_ ?_ ?_ ?_
  · exact Subgroup.mem_subgroupOf.mpr (hVT hv)
  ·
    rintro _ ⟨t, ht, rfl⟩
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have hw : (t : G) * v * (t : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hTV htT) v).mp hv
    have hcomm : (⟨v, hvH⟩ : ↥H) * t * (⟨v, hvH⟩ : ↥H)⁻¹ * t⁻¹ =
        (⟨v, hvH⟩ : ↥H) * (t * (⟨v, hvH⟩ : ↥H) * t⁻¹)⁻¹ := by group
    rcases mem_or_inv_mul_mem hidx hv hvp hw with h5 | h5
    · exact absurd ((Subgroup.mem_normalizer_iff.mp (hT5 htT) v).mpr h5) hvp
    · show ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) * (t : ↥H ⧸ CFSG.pCore 2 ↥H) =
        (t : ↥H ⧸ CFSG.pCore 2 ↥H) * ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)
      rw [mk_comm_iff]
      have hc : v⁻¹ * ((t : G) * v * (t : G)⁻¹) = (t : G) * v * (t : G)⁻¹ * v⁻¹ :=
        congrArg Subtype.val (h.elemAbelian.1.is_comm.comm (⟨v⁻¹, V.inv_mem hv⟩ : ↥V) ⟨_, hw⟩)
      rw [hc] at h5
      have h6 := (F.V5).inv_mem h5
      have e : ((t : G) * v * (t : G)⁻¹ * v⁻¹)⁻¹ = v * (t : G) * v⁻¹ * (t : G)⁻¹ := by group
      rw [e] at h6
      exact h.Vp_le_pCoreOf_and_commutator_le.1 h6
  · intro h1
    exact hvQ ((mk_eq_one_iff _).mp h1)
  · have hv2 : v ^ 2 = 1 := isElemAbelian_pow_eq_one h.elemAbelian hv
    rw [← QuotientGroup.mk_pow, show (⟨v, hvH⟩ : ↥H) ^ 2 = 1 from Subtype.ext (by simpa using hv2),
      QuotientGroup.mk_one]
  ·
    have hle : CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) ≤
        Subgroup.centralizer ({((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)} : Set _) := by
      rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
      refine iSup_le fun q => ?_
      have hq : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
      have : Fact (q : ℕ).Prime := ⟨hq⟩
      by_cases hq2 : (q : ℕ) = 2
      · rw [hq2, hQ.o2]
        exact bot_le
      intro f hf
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective f
      rw [Subgroup.mem_centralizer_singleton_iff]
      set X : Subgroup G := ((CFSG.pCore (q : ℕ) (↥H ⧸ CFSG.pCore 2 ↥H)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype with hX
      have hXH : X ≤ H := Subgroup.map_subtype_le _
      have hXn : H ≤ Subgroup.normalizer (X : Set G) := by
        have hn : (X.subgroupOf H).Normal := by
          have e : X.subgroupOf H = (CFSG.pCore (q : ℕ) (↥H ⧸ CFSG.pCore 2 ↥H)).comap
              (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :=
            Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
          rw [e]
          exact Subgroup.Normal.comap CFSG.pCore_normal _
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mp hn
      have hXr : ∀ x ∈ X, ∃ n : ℕ, x ^ (q : ℕ) ^ n ∈ pCoreOf 2 H := by
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨n, hn⟩ :=
          (CFSG.pCore_isPGroup : IsPGroup (q : ℕ) (CFSG.pCore (q : ℕ) (↥H ⧸ CFSG.pCore 2 ↥H)))
            ⟨_, hz⟩
        refine ⟨n, ?_⟩
        have h1 : ((z ^ (q : ℕ) ^ n : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 := by
          rw [QuotientGroup.mk_pow]
          simpa using congrArg Subtype.val hn
        exact (mk_eq_one_iff _).mp h1
      have hy : (y : G) ∈ X := ⟨y, hf, rfl⟩
      exact ((mk_comm_iff ⟨v, hvH⟩ y).mpr
        (centralizes_of_odd h1222 h1224 F hH hZ hHz hXH hXn hq hq2 hXr v hv y hy)).symm
    exact fun f hf => (Subgroup.mem_centralizer_singleton_iff.mp (hle hf)).symm

end S126L26

end CFSG.Quasithin.H13

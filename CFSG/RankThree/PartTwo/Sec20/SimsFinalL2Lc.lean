module

public import CFSG.RankThree.PartTwo.Sec18.SylowFusion
public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAutQ8
import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.GroupTheory.WielandtProductBasic
public import CFSG.RankThree.PartTwo.Sec20.OneBasics

public section

namespace CFSG.RankThree.PartTwo.Sec20.SimsFinalL2

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_normalizer_zpowers (c : G) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro x hx
  apply CFSG.GroupTheory.WielandtProduct.mem_normalizer_of_forall_conj_mem
  intro z hz
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [(Commute.zpow_right (show Commute x c from Subgroup.mem_centralizer_singleton_iff.mp hx)
    i).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers c i

theorem le_centralizer_of_sec18H {A M H : Subgroup G} {c : G} (hH : Sec18.Sec18H G A M H c) :
    A ≤ Subgroup.centralizer ({c} : Set G) := by
  intro a ha
  have hA := isE27_of_mem_partTwoE hH.mem_partTwoE
  have hcA := (Sec18.mem_and_commutator_mem_of_sec18H hH).1
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))

theorem centralizer_le_normalizer_lc (h1842 : Sec18.Item184_2) {A M H : Subgroup G} {c : G}
    (hH : Sec18.Sec18H G A M H c) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (Sec18.lc H c : Set G) :=
  (centralizer_le_normalizer_zpowers c).trans (Sec18.normalizer_zpowers_le_normalizer_lc h1842 hH)

theorem inf_le_lc {A M H : Subgroup G} {c : G} (hH : Sec18.Sec18H G A M H c) :
    A ⊓ inSubgroup perfectResidual H ≤ Sec18.lc H c :=
  (Sec18.le_sup_and_inf_le_of_sec18H hH).2.trans (Sec18.inSubgroup_perfectResidual_mono le_sup_left)

theorem pCoreOf_lc_le (h1842 : Sec18.Item184_2) {A M H : Subgroup G} {c : G}
    (hH : Sec18.Sec18H G A M H c) : CFSG.Open.pCoreOf 2 (Sec18.lc H c) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Sec18.le_of_le_normalizer_of_isPGroup_two hH.toSec18Std
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ?_
  exact ((le_centralizer_of_sec18H hH).trans (centralizer_le_normalizer_lc h1842 hH)).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

theorem normalizer_sup_pCoreOf_lc_le (h1842 : Sec18.Item184_2) {A M H : Subgroup G} {c : G}
    (hH : Sec18.Sec18H G A M H c) (hAM : A ≤ M)
    (hB3 : IsPGroup 3 (A ⊓ inSubgroup perfectResidual H : Subgroup G))
    (hNB : Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G) ≤ M) :
    Subgroup.normalizer (((A ⊓ inSubgroup perfectResidual H) ⊔
      CFSG.Open.pCoreOf 2 (Sec18.lc H c) : Subgroup G) : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := A ⊓ inSubgroup perfectResidual H with hB
  set O := CFSG.Open.pCoreOf 2 (Sec18.lc H c) with hO
  have hBO : B ≤ Subgroup.normalizer (O : Set G) :=
    (inf_le_lc hH).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Sec18.lc H c)).exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hsyl := Sec20.isSylowOf_sup_of_coprime hB3 hO3 hBO
  have hVM : B ⊔ O ≤ M := sup_le (inf_le_left.trans hAM) (pCoreOf_lc_le h1842 hH)
  intro y hy
  obtain ⟨v, hv, w, hw, rfl⟩ := Sec18.exists_mul_of_isSylowOf hsyl
    (Subgroup.zpowers_le.mpr hy) (Subgroup.mem_zpowers y)
  exact M.mul_mem (hVM hv) (hNB hw)

theorem card_map_inf_lc
    (h1812 : Sec18.Item181_2) (h1841 : Sec18.Item184_1) {A M H : Subgroup G} {c : G}
    (hH : Sec18.Sec18H G A M H c) :
    Nat.card (((A ⊓ inSubgroup perfectResidual H).subgroupOf (Sec18.lc H c)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(Sec18.lc H c)))) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Lc := Sec18.lc H c with hLc
  set B := A ⊓ inSubgroup perfectResidual H with hB
  have hBLc : B ≤ Lc := inf_le_lc hH
  have hB3 : IsPGroup 3 (B.subgroupOf Lc) :=
    (Sec18.SylowFusion.isSylowOf_lc h1812 h1841 hH).isPGroup.comap_subtype
  have h1 := Sec20.card_eq_card_map_mul_inf_ker (QuotientGroup.mk' (CFSG.pCore 2 ↥Lc))
    (B.subgroupOf Lc)
  rw [QuotientGroup.ker_mk', Sec20.card_inf_eq_one_of_isPGroup hB3 CFSG.pCore_isPGroup, mul_one,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBLc).toEquiv,
    Sec18.card_inf_of_sec18H h1812 h1841 hH] at h1
  exact h1.symm

theorem normalizer_map_le_map_inf_lc (h1842 : Sec18.Item184_2) {A M H : Subgroup G} {c : G}
    (hH : Sec18.Sec18H G A M H c) (hAM : A ≤ M)
    (hB3 : IsPGroup 3 (A ⊓ inSubgroup perfectResidual H : Subgroup G))
    (hNB : Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G) ≤ M) :
    Subgroup.normalizer ((((A ⊓ inSubgroup perfectResidual H).subgroupOf (Sec18.lc H c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(Sec18.lc H c))) : Subgroup _) : Set _) ≤
      ((Sec18.lc H c ⊓ M).subgroupOf (Sec18.lc H c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(Sec18.lc H c))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lc := Sec18.lc H c with hLc
  set B := A ⊓ inSubgroup perfectResidual H with hB
  have hO2 := pCoreOf_lc_le h1842 hH
  intro z hz
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
  obtain ⟨y, hy, m, hm, rfl⟩ := Sec20.exists_mul_of_mk_mem_normalizer (inf_le_lc hH) hB3 hz
  have hle : B.subgroupOf Lc ⊔ CFSG.pCore 2 ↥Lc ≤ (Lc ⊓ M).subgroupOf Lc := by
    refine sup_le ?_ ?_
    · intro b hb
      rw [Subgroup.mem_subgroupOf] at hb ⊢
      exact ⟨b.2, hAM hb.1⟩
    · intro b hb
      rw [Subgroup.mem_subgroupOf]
      exact ⟨b.2, hO2 ((Sec18.mem_pCore_iff_mem_pCoreOf b).mp hb)⟩
  refine ⟨y * m, ((Lc ⊓ M).subgroupOf Lc).mul_mem (hle hy) ?_, rfl⟩
  rw [Subgroup.mem_subgroupOf]
  exact ⟨m.2, hNB hm⟩

theorem map_inf_lc_ne_top (h1842 : Sec18.Item184_2) {A M H : Subgroup G} {c : G}
    (hH : Sec18.Sec18H G A M H c) (hLM : ¬ inSubgroup perfectResidual H ≤ M)
    (hO2L : CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) ≤ M) :
    ((Sec18.lc H c ⊓ M).subgroupOf (Sec18.lc H c)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(Sec18.lc H c))) ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lc := Sec18.lc H c with hLc
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥Lc) with hφ
  set Y' := (Lc ⊓ M).subgroupOf Lc with hY'
  have hO2 := pCoreOf_lc_le h1842 hH
  have hker : φ.ker ≤ Y' := by
    rw [hφ, QuotientGroup.ker_mk']
    intro x hx
    rw [hY', Subgroup.mem_subgroupOf]
    exact ⟨x.2, hO2 ((Sec18.mem_pCore_iff_mem_pCoreOf x).mp hx)⟩
  intro htop
  have hLcM : Lc ≤ M := by
    intro x hxL
    have hcomap : (Y'.map φ).comap φ = Y' := by
      rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker]
    have hmem : (⟨x, hxL⟩ : Lc) ∈ (Y'.map φ).comap φ := by
      rw [Subgroup.mem_comap, htop]
      exact Subgroup.mem_top _
    rw [hcomap, hY', Subgroup.mem_subgroupOf] at hmem
    exact hmem.2
  apply hLM
  refine (Sec18.le_sup_and_inf_le_of_sec18H hH).1.trans (sup_le ?_ hO2L)
  exact (Sec18.inSubgroup_perfectResidual_mono le_sup_left).trans hLcM

section Certified


theorem map_inf_lc_eq (h1812 : Sec18.Item181_2) (h1841 : Sec18.Item184_1)
    (h1842 : Sec18.Item184_2) {A M H : Subgroup G} {c : G} (hH : Sec18.Sec18H G A M H c)
    (hAM : A ≤ M)
    (hNB : Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G) ≤ M)
    (hLM : ¬ inSubgroup perfectResidual H ≤ M)
    (hO2L : CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) ≤ M) :
    ((Sec18.lc H c ⊓ M).subgroupOf (Sec18.lc H c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(Sec18.lc H c))) =
      Subgroup.normalizer ((((A ⊓ inSubgroup perfectResidual H).subgroupOf (Sec18.lc H c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(Sec18.lc H c))) : Subgroup _) : Set _) := by
  obtain ⟨e⟩ := Sec18.SylowFusion.nonempty_quotient_lc h1841 hH
  have hB3 : IsPGroup 3 (A ⊓ inSubgroup perfectResidual H : Subgroup G) :=
    (Sec18.SylowFusion.isSylowOf_lc h1812 h1841 hH).isPGroup
  exact KFacts.L34Max.eq_normalizer_of_normalizer_le e (card_map_inf_lc h1812 h1841 hH)
    (normalizer_map_le_map_inf_lc h1842 hH hAM hB3 hNB) (map_inf_lc_ne_top h1842 hH hLM hO2L)

end Certified

omit [Finite G] in
theorem isSylowOf_map_hom {G' : Type*} [Group G'] [Finite G] {p : ℕ} [Fact p.Prime]
    (φ : G →* G') {P K : Subgroup G} (h : CFSG.ABGLocalTools.IsSylowOf p P K) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map φ) (K.map φ) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (φ.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem isSylowOf_inf_lc (h1842 : Sec18.Item184_2) {A M H T : Subgroup G} {c : G}
    (hH : Sec18.Sec18H G A M H c)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ Subgroup.centralizer {c})
      (M ⊓ Subgroup.centralizer {c})) :
    CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ Subgroup.centralizer {c} ⊓ (Sec18.lc H c ⊓ M))
      (Sec18.lc H c ⊓ M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hT.inf_of_le_normalizer ?_ ?_
  · exact le_inf inf_le_right (inf_le_left.trans (Sec18.SylowFusion.lc_le_centralizer H c))
  · intro g hg
    exact Sec20.mem_normalizer_inf_of_mem (centralizer_le_normalizer_lc h1842 hH hg.2)
      (Subgroup.le_normalizer hg.1)

section Certified


theorem card_map_sylow_eq_eight (h1812 : Sec18.Item181_2) (h1841 : Sec18.Item184_1)
    (h1842 : Sec18.Item184_2) {A M H T : Subgroup G} {c : G} (hH : Sec18.Sec18H G A M H c)
    (hAM : A ≤ M)
    (hNB : Subgroup.normalizer ((A ⊓ inSubgroup perfectResidual H : Subgroup G) : Set G) ≤ M)
    (hLM : ¬ inSubgroup perfectResidual H ≤ M)
    (hO2L : CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H) ≤ M)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ Subgroup.centralizer {c})
      (M ⊓ Subgroup.centralizer {c})) :
    Nat.card (((T ⊓ Subgroup.centralizer {c} ⊓ (Sec18.lc H c ⊓ M)).subgroupOf
        (Sec18.lc H c)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Sec18.lc H c)))) = 8 ∧
      ((T ⊓ Subgroup.centralizer {c} ⊓ (Sec18.lc H c ⊓ M)).subgroupOf
        (Sec18.lc H c)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(Sec18.lc H c))) ≤
      Subgroup.normalizer ((((A ⊓ inSubgroup perfectResidual H).subgroupOf (Sec18.lc H c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥(Sec18.lc H c))) : Subgroup _) : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lc := Sec18.lc H c with hLc
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥Lc) with hφ
  set Tc := T ⊓ Subgroup.centralizer {c} ⊓ (Lc ⊓ M) with hTc
  have hsyl := isSylowOf_inf_lc h1842 hH hT
  have hTcLc : Tc ≤ Lc := inf_le_right.trans inf_le_left
  have hsyl' : CFSG.ABGLocalTools.IsSylowOf 2 (Tc.subgroupOf Lc) ((Lc ⊓ M).subgroupOf Lc) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff Lc, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTcLc, inf_eq_left.mpr inf_le_left]
    exact hsyl
  have hsylQ := isSylowOf_map_hom φ hsyl'
  rw [map_inf_lc_eq h1812 h1841 h1842 hH hAM hNB hLM hO2L] at hsylQ
  obtain ⟨e⟩ := Sec18.SylowFusion.nonempty_quotient_lc h1841 hH
  have h72 := KFacts.L34Max.card_normalizer_of_card_eq_nine e (card_map_inf_lc h1812 h1841 hH)
  refine ⟨?_, hsylQ.le⟩
  rw [hsylQ.card_eq, h72]
  have : (72 : ℕ).factorization 2 = 3 := by
    rw [show (72 : ℕ) = 2 ^ 3 * 9 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [this]
  norm_num

end Certified

@[expose] noncomputable def rho (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) →* MulAut (K ⧸ CFSG.pCore 2 K) :=
  (Res6.quotAut K).comp K.normalizerMonoidHom

omit [Finite G] in
theorem rho_apply_mk (K : Subgroup G) (y : Subgroup.normalizer (K : Set G)) (x : K) :
    rho K y (QuotientGroup.mk' (CFSG.pCore 2 K) x) =
      QuotientGroup.mk' (CFSG.pCore 2 K)
        ⟨(y : G) * x * (y : G)⁻¹, (Subgroup.mem_normalizer_iff.mp y.2 x).mp x.2⟩ :=
  rfl

omit [Finite G] in
theorem rho_eq_conj (K : Subgroup G) {t : G} (ht : t ∈ K) :
    rho K ⟨t, Subgroup.le_normalizer ht⟩ =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 K) ⟨t, ht⟩) := by
  apply MulEquiv.ext
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
  rw [rho_apply_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem mem_normalizer_of_rho_eq_one {K B : Subgroup G} (hBK : B ≤ K)
    {y : Subgroup.normalizer (K : Set G)} (hy : rho K y = 1) :
    (y : G) ∈ Subgroup.normalizer ((B ⊔ CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Sec20.mem_normalizer_of_map_conj_le
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨b, hb, rfl⟩
    have hbK : b ∈ K := hBK hb
    have h1 := rho_apply_mk K y ⟨b, hbK⟩
    rw [hy, MulAut.one_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    have h2 := (Sec18.mem_pCore_iff_mem_pCoreOf _).mp h1
    change (y : G) * b * (y : G)⁻¹ ∈ B ⊔ CFSG.Open.pCoreOf 2 K
    have h3 : (y : G) * b * (y : G)⁻¹ = b * ((b : G)⁻¹ * ((y : G) * b * (y : G)⁻¹)) := by group
    rw [h3]
    refine Subgroup.mul_mem_sup hb ?_
    simpa using h2
  · refine le_trans ?_ le_sup_right
    rintro _ ⟨o, ho, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K y.2) o).mp ho

omit [Finite G] in
theorem rho_mem_normalizer_map {K S : Subgroup G} {t : Subgroup.normalizer (K : Set G)}
    (ht : (t : G) ∈ Subgroup.normalizer (S : Set G)) :
    rho K t ∈ Subgroup.normalizer
      (((S.subgroupOf (Subgroup.normalizer (K : Set G))).map (rho K) : Subgroup _) : Set _) := by
  have key : ∀ u : Subgroup.normalizer (K : Set G), (u : G) ∈ Subgroup.normalizer (S : Set G) →
      ∀ z ∈ (S.subgroupOf (Subgroup.normalizer (K : Set G))).map (rho K),
        rho K u * z * (rho K u)⁻¹ ∈ (S.subgroupOf (Subgroup.normalizer (K : Set G))).map (rho K) := by
    rintro u hu _ ⟨s, hs, rfl⟩
    refine ⟨u * s * u⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hs
    show u * s * u⁻¹ ∈ S.subgroupOf _
    rw [Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp hu (s : G)).mp hs
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact key t ht z
  · intro hz
    have ht' : ((t⁻¹ : Subgroup.normalizer (K : Set G)) : G) ∈
        Subgroup.normalizer (S : Set G) := by
      simpa using (Subgroup.normalizer (S : Set G)).inv_mem ht
    have h1 := key t⁻¹ ht' _ hz
    have e : rho K t⁻¹ * (rho K t * z * (rho K t)⁻¹) * (rho K t⁻¹)⁻¹ = z := by
      rw [map_inv]
      group
    rwa [e] at h1

end CFSG.RankThree.PartTwo.Sec20.SimsFinalL2

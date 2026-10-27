module

public import CFSG.Quasithin.H13.NQBlockFiveModelTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Offender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellPrime
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.Quasithin.H13.NQBlockOriginalSupplements
public import CFSG.Quasithin.SteinbergCDSmallDegreeNormalizer

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LinearGroups.UnitaryThreeOverNine CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.Quasithin.SteinbergCD
  (odd_characteristic_degree_three_large_prime_normalizers_centralize_two_subgroups)

theorem factorization_two_eq {k i n : ℕ} (h : 2 ^ k * i = n) (hi : ¬ 2 ∣ i) :
    n.factorization 2 = k := by
  subst h
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) (by rintro rfl; exact hi (dvd_zero 2)),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hi, add_zero]

theorem card_sylow_two_eq {S : Type*} [Group S] [Finite S] {k i : ℕ}
    (hS : Nat.card S = 2 ^ k * i) (hi : ¬ 2 ∣ i) (P : Sylow 2 S) :
    Nat.card (P : Subgroup S) = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [P.card_eq_multiplicity, factorization_two_eq hS.symm hi]

theorem prime_dvd_half_order {s : ℕ} (hs : s.Prime) (hs5 : 5 ≤ s) : s ∣ s * (s ^ 2 - 1) / 2 := by
  have hodd : 2 ∣ s ^ 2 - 1 := by
    obtain ⟨m, hm⟩ := hs.odd_of_ne_two (by omega)
    subst hm
    exact ⟨2 * m ^ 2 + 2 * m, by ring_nf; omega⟩
  rw [Nat.mul_div_assoc _ hodd]
  exact dvd_mul_right s _

variable {G : Type} [Group G] [Finite G]

theorem original_K_quotient_facts {T L M : Subgroup G}
    (h : QTNQ T L M) :
    nqOriginalK T L ≤ L ∧ T ≤ normalizer (nqOriginalK T L : Set G) ∧
      ⁅nqOriginalK T L, nqOriginalK T L⁆ = nqOriginalK T L ∧
      IsSimpleGroup (nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L)) ∧
      (∃ a b : nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L), a * b ≠ b * a) ∧
      ∃ s : ℕ, s.Prime ∧ 5 ≤ s ∧
        Nonempty (nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod s)) ∧
        Nat.card (nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L)) = s * (s ^ 2 - 1) / 2 := by
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.t_le.trans h.eq_normalizer.le)
  obtain ⟨hKL, hTK, -⟩ := original_K_supplement h
  have hKp := (original_radical_supplement h.sylow.1 h.maximal_local.1.2.2.1
    (h.eq_normalizer ▸ h.t_le) h.maximal_local.1.2.1 hR).2.2.2.2.2.2.2.1
  obtain ⟨-, -, -, -, ⟨e, -⟩, ⟨s, hsf, hs5, ⟨e'⟩⟩, -⟩ :=
    original_radical_supplements_share_simple_residual_and_internal_module h hR
  have hs : s.Prime := hsf.out
  have hs2 : s ≠ 2 := by omega
  have : IsSimpleGroup (projectiveSL 2 (ZMod s)) :=
    CFSG.QuasithinUnique.Setup.Family.p2_isSimpleGroup hs5
  have hsimp : IsSimpleGroup (nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L)) :=
    MulEquiv.isSimpleGroup (e.trans e')
  have : Group.IsPerfect (nqOriginalK T L) := isPerfect_iff.mpr hKp
  have hperf : Group.IsPerfect (nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  refine ⟨hKL, hTK, hKp, hsimp, ?_, s, hs, hs5,
    ⟨e.trans (e'.trans (CFSG.QuasithinUnique.Setup.Family.p2Equiv (ZMod s)))⟩, ?_⟩
  · by_contra hc
    simp only [not_exists, ne_eq, not_not] at hc
    have hbot : commutator (nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L)) = ⊥ := by
      rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [mem_centralizer_iff]
      intro y _
      exact (hc x y).symm
    rw [Group.isPerfect_def.mp hperf] at hbot
    obtain ⟨x, hx⟩ := exists_ne (1 : nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L))
    exact hx (mem_bot.mp (hbot ▸ mem_top x))
  · rw [Nat.card_congr (e.trans e').toEquiv, CFSG.QuasithinUnique.Setup.Family.p2_card hs2]

theorem core_image_facts {K A S : Type*} [Group K] [Finite K] [Group A] [Group S]
    [IsSimpleGroup (K ⧸ CFSG.pCore 2 K)] (hnab : ∃ a b : K ⧸ CFSG.pCore 2 K, a * b ≠ b * a)
    (ι : K →* A) (hι : Function.Injective ι) (θ : A →* S) [Group.IsSolvable θ.ker] :
    (θ.comp ι).ker ≤ CFSG.pCore 2 K ∧
      Nat.card (θ.comp ι).range =
        Nat.card ((CFSG.pCore 2 K).map (θ.comp ι)) * Nat.card (K ⧸ CFSG.pCore 2 K) := by
  have hsolv : Group.IsSolvable (θ.comp ι).ker := by
    let f : (θ.comp ι).ker →* θ.ker :=
      (ι.comp (θ.comp ι).ker.subtype).codRestrict θ.ker fun x => by
        have hx := x.2
        rw [MonoidHom.mem_ker] at hx ⊢
        exact hx
    have hf : Function.Injective f := fun x y hxy =>
      Subtype.ext (hι (congrArg Subtype.val hxy))
    exact Group.isSolvable_of_isSolvable_injective hf
  have hker := le_pCore_of_isSolvable_of_normal hnab (θ.comp ι).ker
  exact ⟨hker, card_range_eq_of_ker_le_pCore _ hker⟩

omit [Finite G] in
theorem range_inclusion_eq {K A : Subgroup G} (hKA : K ≤ A) :
    (inclusion hKA).range = K.subgroupOf A := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

omit [Finite G] in
theorem subgroupOf_le_normalizer_subgroupOf {Y Z L : Subgroup G}
    (hYZ : Y ≤ normalizer (Z : Set G)) :
    Y.subgroupOf L ≤ normalizer ((Z.subgroupOf L : Subgroup L) : Set L) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro a
  rw [mem_subgroupOf, mem_subgroupOf]
  simpa using mem_normalizer_iff.mp (hYZ (mem_subgroupOf.mp hx)) (a : G)

theorem exists_sylow_two_le_normalizer {T K A H : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hTH : T ≤ H) (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal)
    (hTK : T ≤ normalizer (K : Set G)) :
    ∃ T₀ : Sylow 2 A, (T₀ : Subgroup A) ≤ normalizer ((K.subgroupOf A : Subgroup A) : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTtop : IsSylowOf 2 T ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, hT.1, hT.2⟩
  have hHA : H ≤ normalizer (A : Set G) := (normal_subgroupOf_iff_le_normalizer hAH).mp hAn
  have hTA : IsSylowOf 2 (T ⊓ A) A := (hTtop.of_le hTH le_top).inf_of_le_normalizer hAH hHA
  obtain ⟨T₀, hT₀⟩ := hTA.exists_sylow_eq_subgroupOf
  refine ⟨T₀, ?_⟩
  rw [hT₀]
  exact subgroupOf_le_normalizer_subgroupOf (inf_le_left.trans hTK)

theorem false_of_surjective_three_sixty {T L M : Subgroup G}
    (h : QTNQ T L M) {H A : Subgroup G} (hKTH : nqOriginalK T L ⊔ T ≤ H) (hAH : A ≤ H)
    (hAn : (A.subgroupOf H).Normal) (hKA : nqOriginalK T L ≤ A) {S : Type*} [Group S] [Finite S]
    [IsSimpleGroup S] (hS : Nat.card S = 360) (θ : A →* S) (hθ : Function.Surjective θ)
    [Group.IsSolvable θ.ker] : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hTK, -, hsimp, hnab, s, hs, hs5, -, hcard⟩ := original_K_quotient_facts h
  obtain ⟨-, hB⟩ := core_image_facts hnab (inclusion hKA) (inclusion_injective hKA) θ
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup.map (θ.comp (inclusion hKA)) :
    IsPGroup 2 ((CFSG.pCore 2 (nqOriginalK T L)).map (θ.comp (inclusion hKA)))).exists_card_eq
  rw [ha, hcard] at hB
  have hB360 : 2 ^ a * (s * (s ^ 2 - 1) / 2) ∣ 360 := hB ▸ hS ▸ card_subgroup_dvd_card _
  have hs360 : s ∣ 360 :=
    (prime_dvd_half_order hs hs5).trans ((dvd_mul_left _ _).trans hB360)
  have hs5' : s = 5 := by
    have h360 : (360 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 := by norm_num
    rw [h360] at hs360
    rcases (Nat.Prime.dvd_mul hs).mp hs360 with h1 | h1
    · rcases (Nat.Prime.dvd_mul hs).mp h1 with h2 | h2
      · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h2)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp (hs.dvd_of_dvd_pow h2)
        omega
    · exact (Nat.prime_dvd_prime_iff_eq hs Nat.prime_five).mp h1
  subst hs5'
  obtain ⟨T₀, hT₀⟩ := exists_sylow_two_le_normalizer h.sylow (le_sup_right.trans hKTH) hAH hAn hTK
  let S₂ := T₀.mapSurjective hθ
  have hS₂ : Nat.card (S₂ : Subgroup S) = 8 :=
    card_sylow_two_eq (k := 3) (i := 45) (by rw [hS]; norm_num) (by decide) S₂
  have hS₂B : (S₂ : Subgroup S) ≤ normalizer ((θ.comp (inclusion hKA)).range : Set S) := by
    rw [Sylow.coe_mapSurjective, MonoidHom.range_comp, range_inclusion_eq]
    exact (map_mono hT₀).trans (le_normalizer_map θ)
  exact false_of_card_three_sixty hS (a := a) (by rw [hB]; norm_num) hS₂ hS₂B

theorem false_of_surjective_SU33 {T L M : Subgroup G}
    (h : QTNQ T L M) {H A : Subgroup G} (hKTH : nqOriginalK T L ⊔ T ≤ H) (hAH : A ≤ H)
    (hAn : (A.subgroupOf H).Normal) (hKA : nqOriginalK T L ≤ A) {F : Type} [Field F]
    (hF : Nat.card F = 9) (θ : A →* StatedSU 3 3 F) (hθ : Function.Surjective θ)
    [Group.IsSolvable θ.ker] : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  obtain ⟨-, hTK, hKp, hsimp, hnab, s, hs, hs5, ⟨eK⟩, hcard⟩ := original_K_quotient_facts h
  obtain ⟨hker, hB⟩ := core_image_facts hnab (inclusion hKA) (inclusion_injective hKA) θ
  have hV2 : IsPGroup 2 ((CFSG.pCore 2 (nqOriginalK T L)).map (θ.comp (inclusion hKA))) :=
    CFSG.pCore_isPGroup.map _
  obtain ⟨a, ha⟩ := hV2.exists_card_eq
  have hS : Nat.card (StatedSU 3 3 F) = 6048 := card_statedSU hF
  have hBdvd : Nat.card (θ.comp (inclusion hKA)).range ∣ 6048 :=
    hS ▸ card_subgroup_dvd_card _
  have hs7 : s = 7 := by
    have h1 : s ∣ 6048 :=
      (prime_dvd_half_order hs hs5).trans (hcard ▸ ((dvd_mul_left _ _).trans (hB ▸ hBdvd)))
    have h6048 : (6048 : ℕ) = 2 ^ 5 * 3 ^ 3 * 7 := by norm_num
    rw [h6048] at h1
    rcases (Nat.Prime.dvd_mul hs).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hs).mp h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp (hs.dvd_of_dvd_pow h3)
        omega
    · exact (Nat.prime_dvd_prime_iff_eq hs (by norm_num)).mp h2
  subst hs7
  have h7B : 7 ∣ Nat.card (θ.comp (inclusion hKA)).range := by
    rw [hB, hcard]
    exact Dvd.dvd.mul_left (by norm_num) _
  have hnoinv : ∀ t : StatedSU 3 3 F, orderOf t = 2 →
      ¬ (θ.comp (inclusion hKA)).range ≤ centralizer ({t} : Set (StatedSU 3 3 F)) := by
    intro t ht hBt
    have h96 := card_dvd_of_le hBt
    rw [card_centralizer_of_orderOf_eq_two hF ht] at h96
    exact absurd (h7B.trans h96) (by decide)
  have hBV : (θ.comp (inclusion hKA)).range ≤ normalizer
      (((CFSG.pCore 2 (nqOriginalK T L)).map (θ.comp (inclusion hKA)) : Subgroup _) :
        Set (StatedSU 3 3 F)) := by
    rintro _ ⟨k, rfl⟩
    rw [mem_normalizer_iff]
    intro v
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨k * q * k⁻¹, (CFSG.pCore_normal (p := 2)).conj_mem q hq k, by simp⟩
    · rintro ⟨q, hq, hqv⟩
      refine ⟨k⁻¹ * q * k⁻¹⁻¹, (CFSG.pCore_normal (p := 2)).conj_mem q hq k⁻¹, ?_⟩
      rw [map_mul, map_mul, map_inv, inv_inv, hqv]
      group
  have h2F : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    have h9 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
    rw [← Nat.card_eq_fintype_card, hF] at h9
    have h3 : (3 : F) = 0 := by
      have h32 : (3 : F) ^ 2 = 0 := by
        push_cast at h9
        linear_combination h9
      exact (pow_eq_zero_iff two_ne_zero).mp h32
    intro h2
    exact one_ne_zero (by linear_combination h3 - h2 : (1 : F) = 0)
  have h7cent : ∀ y ∈ (θ.comp (inclusion hKA)).range, orderOf y = 7 →
      y ∈ centralizer (((CFSG.pCore 2 (nqOriginalK T L)).map (θ.comp (inclusion hKA)) :
        Subgroup _) : Set (StatedSU 3 3 F)) := by
    intro y hyB hy7
    have hP : IsPGroup 7 ((zpowers y).map (StatedSU 3 3 F).subtype) :=
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy7, pow_one])).map _
    have hPQ : (zpowers y).map (StatedSU 3 3 F).subtype ≤ normalizer
        ((((CFSG.pCore 2 (nqOriginalK T L)).map (θ.comp (inclusion hKA))).map
          (StatedSU 3 3 F).subtype : Subgroup _) : Set (GL (Fin 3) F)) :=
      (map_mono (zpowers_le.mpr (hBV hyB))).trans (le_normalizer_map _)
    have hc := odd_characteristic_degree_three_large_prime_normalizers_centralize_two_subgroups
      h2F le_rfl (hV2.map _) (by norm_num) (by norm_num) hP hPQ
    rw [← map_commutator, map_eq_bot_iff_of_injective _ (StatedSU 3 3 F).subtype_injective,
      commutator_eq_bot_iff_le_centralizer] at hc
    exact hc (mem_zpowers y)
  have hBcent : (θ.comp (inclusion hKA)).range ≤ centralizer
      (((CFSG.pCore 2 (nqOriginalK T L)).map (θ.comp (inclusion hKA)) : Subgroup _) :
        Set (StatedSU 3 3 F)) := by
    set V := (CFSG.pCore 2 (nqOriginalK T L)).map (θ.comp (inclusion hKA)) with hVdef
    set φ := θ.comp (inclusion hKA) with hφdef
    have hDn : ((centralizer (V : Set (StatedSU 3 3 F))).comap φ).Normal := by
      constructor
      intro x hx k
      rw [mem_comap, mem_centralizer_iff] at hx ⊢
      intro v hv
      have hkV := mem_normalizer_iff.mp (hBV ⟨k, rfl⟩) (φ k⁻¹ * v * (φ k⁻¹)⁻¹)
      have hv' : φ k⁻¹ * v * (φ k⁻¹)⁻¹ ∈ V := by
        have := mem_normalizer_iff.mp (hBV ⟨k⁻¹, rfl⟩) v
        exact this.mp hv
      have h1 := hx _ hv'
      rw [map_mul, map_mul, map_inv]
      rw [map_inv, inv_inv] at h1
      calc v * (φ k * φ x * (φ k)⁻¹)
          = φ k * (((φ k)⁻¹ * v * φ k) * φ x) * (φ k)⁻¹ := by group
        _ = φ k * (φ x * ((φ k)⁻¹ * v * φ k)) * (φ k)⁻¹ := by rw [h1]
        _ = φ k * φ x * (φ k)⁻¹ * v := by group
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((centralizer (V : Set (StatedSU 3 3 F))).comap φ).map
        (QuotientGroup.mk' (CFSG.pCore 2 (nqOriginalK T L)))) with h0 | h1
    · exfalso
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 7 h7B
      obtain ⟨k, hk⟩ := y.2
      have hkD : k ∈ (centralizer (V : Set (StatedSU 3 3 F))).comap φ := by
        rw [mem_comap, hk]
        exact h7cent _ y.2 (by rw [Subgroup.orderOf_coe]; exact hy)
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h0
      have hyV : (y : StatedSU 3 3 F) ∈ V := ⟨k, h0 hkD, hk⟩
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hV2) ⟨y, hyV⟩
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hy] at hj
      rcases j with _ | j
      · norm_num at hj
      · have h27 : 2 ∣ 7 := ⟨2 ^ j, by rw [hj, pow_succ]; ring⟩
        omega
    · have h2q : IsPGroup 2
          (nqOriginalK T L ⧸ (centralizer (V : Set (StatedSU 3 3 F))).comap φ) := by
        refine IsPGroup.of_surjective (CFSG.pCore_isPGroup :
          IsPGroup 2 (CFSG.pCore 2 (nqOriginalK T L)))
          ((QuotientGroup.mk' _).comp (CFSG.pCore 2 (nqOriginalK T L)).subtype) ?_
        intro z
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
        have hx : QuotientGroup.mk' (CFSG.pCore 2 (nqOriginalK T L)) x ∈
            ((centralizer (V : Set (StatedSU 3 3 F))).comap φ).map
              (QuotientGroup.mk' (CFSG.pCore 2 (nqOriginalK T L))) := h1 ▸ mem_top _
        obtain ⟨y, hy, hyx⟩ := hx
        have hq : y⁻¹ * x ∈ CFSG.pCore 2 (nqOriginalK T L) := QuotientGroup.eq.mp hyx
        refine ⟨⟨y⁻¹ * x, hq⟩, ?_⟩
        have hy1 : QuotientGroup.mk' ((centralizer (V : Set (StatedSU 3 3 F))).comap φ) y⁻¹ = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (inv_mem hy)
        change QuotientGroup.mk' _ (y⁻¹ * x) = QuotientGroup.mk' _ x
        rw [map_mul, hy1, one_mul]
      have hperfK : Group.IsPerfect (nqOriginalK T L) := isPerfect_iff.mpr hKp
      have htop := CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_isPerfect hperfK _ h2q
      rintro _ ⟨k, rfl⟩
      exact mem_comap.mp (htop ▸ mem_top k)
  have hV1 : (CFSG.pCore 2 (nqOriginalK T L)).map (θ.comp (inclusion hKA)) = ⊥ := by
    by_contra hV
    have h2V : 2 ∣ Nat.card ((CFSG.pCore 2 (nqOriginalK T L)).map (θ.comp (inclusion hKA))) := by
      rw [ha]
      rcases a with _ | a
      · exfalso
        apply hV
        rw [← card_eq_one, ha, pow_zero]
      · exact dvd_pow_self 2 (Nat.succ_ne_zero a)
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2V
    refine hnoinv t (by rw [← Subgroup.orderOf_coe] at ht; exact ht) (hBcent.trans ?_)
    exact centralizer_le (Set.singleton_subset_iff.mpr t.2)
  have hkerφ : (θ.comp (inclusion hKA)).ker = CFSG.pCore 2 (nqOriginalK T L) := by
    refine le_antisymm hker fun x hx => ?_
    have hxV : (θ.comp (inclusion hKA)) x ∈
        (CFSG.pCore 2 (nqOriginalK T L)).map (θ.comp (inclusion hKA)) := ⟨x, hx, rfl⟩
    rw [hV1, mem_bot] at hxV
    exact hxV
  have hB168 : Nat.card (θ.comp (inclusion hKA)).range = 168 := by
    rw [hB, hV1, card_bot, one_mul, hcard]
    norm_num
  let eB : (θ.comp (inclusion hKA)).range ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    (QuotientGroup.quotientKerEquivRange _).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerφ).trans eK)
  have hAut : Nat.card (MulAut (θ.comp (inclusion hKA)).range) ∣ 336 := by
    have hout : Nat.card (Outer (θ.comp (inclusion hKA)).range) ∣ 2 := by
      have h1 := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor (p := 7)
        (f := 1) (by norm_num) (ZMod 7) (by rw [Nat.card_zmod]; norm_num)).2 _ ⟨eB⟩
      norm_num at h1
      exact h1
    have hinn : Nat.card (inner (θ.comp (inclusion hKA)).range) ∣ 168 := by
      have h1 := card_range_dvd
        (MulAut.conj : (θ.comp (inclusion hKA)).range →* MulAut (θ.comp (inclusion hKA)).range)
      rwa [hB168] at h1
    rw [card_eq_card_quotient_mul_card_subgroup (inner (θ.comp (inclusion hKA)).range)]
    exact Nat.mul_dvd_mul hout hinn
  obtain ⟨T₀, hT₀⟩ :=
    exists_sylow_two_le_normalizer h.sylow (le_sup_right.trans hKTH) hAH hAn hTK
  have hS₂ : Nat.card ((T₀.mapSurjective hθ : Sylow 2 _) : Subgroup (StatedSU 3 3 F)) = 32 :=
    card_sylow_two_eq (k := 5) (i := 189) (by rw [hS]; norm_num) (by decide) _
  have hS₂B : ((T₀.mapSurjective hθ : Sylow 2 _) : Subgroup (StatedSU 3 3 F)) ≤
      normalizer ((θ.comp (inclusion hKA)).range : Set (StatedSU 3 3 F)) := by
    rw [Sylow.coe_mapSurjective, MonoidHom.range_comp, range_inclusion_eq]
    exact (map_mono hT₀).trans (le_normalizer_map θ)
  let c := ((θ.comp (inclusion hKA)).range).normalizerMonoidHom.comp (inclusion hS₂B)
  have hc : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hx1
    have hxB : (θ.comp (inclusion hKA)).range ≤
        centralizer ({(x : StatedSU 3 3 F)} : Set (StatedSU 3 3 F)) := by
      intro b hb
      rw [mem_centralizer_singleton_iff]
      have h1 := DFunLike.congr_fun hx ⟨b, hb⟩
      have h2 : (x : StatedSU 3 3 F) * b * (x : StatedSU 3 3 F)⁻¹ = b := congrArg Subtype.val h1
      calc b * x = ((x : StatedSU 3 3 F) * b * (x : StatedSU 3 3 F)⁻¹) * x := by rw [h2]
        _ = x * b := by group
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (T₀.mapSurjective hθ).isPGroup') x
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.mp (by rw [hk, pow_zero]))
    have hxo : orderOf (x : StatedSU 3 3 F) = 2 ^ k := by rw [Subgroup.orderOf_coe, hk]
    have ht := orderOf_pow_orderOf_div (x := (x : StatedSU 3 3 F)) (n := 2)
      (by rw [hxo]; positivity) (by rw [hxo]; exact dvd_pow_self 2 hk0)
    refine hnoinv _ ht fun b hb => ?_
    rw [mem_centralizer_singleton_iff]
    have hbx := hxB hb
    rw [mem_centralizer_singleton_iff] at hbx
    exact (Commute.pow_right hbx _).eq
  have h32 : Nat.card ((T₀.mapSurjective hθ : Sylow 2 _) : Subgroup (StatedSU 3 3 F)) ∣
      Nat.card (MulAut (θ.comp (inclusion hKA)).range) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hc).toEquiv]
    exact card_subgroup_dvd_card _
  rw [hS₂] at h32
  exact absurd (h32.trans hAut) (by decide)

theorem eq_original_K_of_surjective {T L M : Subgroup G}
    (h : QTNQ T L M) {H A : Subgroup G} (hKTH : nqOriginalK T L ⊔ T ≤ H) (hAH : A ≤ H)
    (hAn : (A.subgroupOf H).Normal) (hAp : ⁅A, A⁆ = A) (hKA : nqOriginalK T L ≤ A)
    {S : Type*} [Group S] [Finite S] (θ : A →* S) (hker : θ.ker = CFSG.pCore 2 A)
    (hS : ∀ s : ℕ, s.Prime → 5 ≤ s → s ∣ Nat.card S → s * (s ^ 2 - 1) / 2 = Nat.card S) :
    A = nqOriginalK T L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsSolvable θ.ker := by
    rw [hker]
    have := (CFSG.pCore_isPGroup (p := 2) (G := A)).isNilpotent
    infer_instance
  obtain ⟨-, hTK, -, hsimp, hnab, s, hs, hs5, -, hcard⟩ := original_K_quotient_facts h
  obtain ⟨-, hB⟩ := core_image_facts hnab (inclusion hKA) (inclusion_injective hKA) θ
  have hBS : Nat.card (θ.comp (inclusion hKA)).range ∣ Nat.card S := card_subgroup_dvd_card _
  have hsS : s ∣ Nat.card S :=
    (prime_dvd_half_order hs hs5).trans (hcard ▸ ((dvd_mul_left _ _).trans (hB ▸ hBS)))
  have hKS : Nat.card (nqOriginalK T L ⧸ CFSG.pCore 2 (nqOriginalK T L)) = Nat.card S := by
    rw [hcard, hS s hs hs5 hsS]
  have hrange : (θ.comp (inclusion hKA)).range = ⊤ := by
    apply eq_top_of_card_eq
    refine le_antisymm (Nat.le_of_dvd Nat.card_pos hBS) ?_
    rw [hB, hKS]
    exact Nat.le_mul_of_pos_left _ Nat.card_pos
  have hHA : H ≤ normalizer (A : Set G) := (normal_subgroupOf_iff_le_normalizer hAH).mp hAn
  have hQA2 : IsPGroup 2 ((CFSG.pCore 2 A).map A.subtype) := CFSG.pCore_isPGroup.map _
  have hNQ : normalizer (A : Set G) ≤ normalizer (((CFSG.pCore 2 A).map A.subtype : Subgroup G) :
      Set G) := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hTH : T ≤ H := le_sup_right.trans hKTH
  have hQT : (CFSG.pCore 2 A).map A.subtype ≤ T := by
    let T' : Sylow 2 G := h.sylow.1.toSylow h.sylow.2
    have hT' : (T' : Subgroup G) = T := IsPGroup.toSylow_coe _ _
    have h1 := T'.is_maximal' (T'.isPGroup'.to_sup_of_normal_right' hQA2
      (by rw [hT']; exact hTH.trans (hHA.trans hNQ))) le_sup_left
    rw [← hT', ← h1]
    exact le_sup_right
  have hfac : ∀ x : A, ∃ k : nqOriginalK T L, ∃ q ∈ CFSG.pCore 2 A, x = inclusion hKA k * q := by
    intro x
    have hx : θ x ∈ (θ.comp (inclusion hKA)).range := hrange ▸ mem_top _
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, (inclusion hKA k)⁻¹ * x, ?_, by group⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
    change (θ (inclusion hKA k))⁻¹ * θ x = 1
    rw [← hk]
    exact inv_mul_cancel _
  have hAK : A ≤ normalizer (nqOriginalK T L : Set G) := by
    intro x hx
    obtain ⟨k, q, hq, hkq⟩ := hfac ⟨x, hx⟩
    have hx' : x = (k : G) * ((q : A) : G) := congrArg Subtype.val hkq
    rw [hx']
    exact mul_mem (le_normalizer k.2) (hTK (hQT ⟨q, hq, rfl⟩))
  have hKn : ((nqOriginalK T L).subgroupOf A).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKA).mpr hAK
  have h2q : IsPGroup 2 (A ⧸ (nqOriginalK T L).subgroupOf A) := by
    refine IsPGroup.of_surjective (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 A))
      ((QuotientGroup.mk' _).comp (CFSG.pCore 2 A).subtype) ?_
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
    obtain ⟨k, q, hq, hkq⟩ := hfac x
    refine ⟨⟨q, hq⟩, ?_⟩
    have hk1 : QuotientGroup.mk' ((nqOriginalK T L).subgroupOf A) (inclusion hKA k) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr k.2
    change QuotientGroup.mk' _ q = QuotientGroup.mk' _ x
    rw [hkq, map_mul, hk1, one_mul]
  have hperfA : Group.IsPerfect A := isPerfect_iff.mpr hAp
  have htop := CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_isPerfect hperfA _ h2q
  refine le_antisymm (fun x hx => ?_) hKA
  have hx : (⟨x, hx⟩ : A) ∈ (nqOriginalK T L).subgroupOf A := htop ▸ mem_top _
  exact hx

theorem prime_eq_of_dvd_two_three {s q a b : ℕ} (hs : s.Prime) (hs5 : 5 ≤ s) (hq : q.Prime)
    (h : s ∣ 2 ^ a * 3 ^ b * q) : s = q := by
  rcases (Nat.Prime.dvd_mul hs).mp h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hs).mp h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h2)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp (hs.dvd_of_dvd_pow h2)
      omega
  · exact (Nat.prime_dvd_prime_iff_eq hs hq).mp h1

theorem isSolvable_ker_comp_center {A : Type*} [Group A] (N : Subgroup A) [N.Normal]
    [Group.IsSolvable N] :
    Group.IsSolvable ((QuotientGroup.mk' (center (A ⧸ N))).comp (QuotientGroup.mk' N)).ker := by
  have hNk : N ≤ ((QuotientGroup.mk' (center (A ⧸ N))).comp (QuotientGroup.mk' N)).ker :=
    fun x hx => by
      have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h1, map_one]
  let g : ((QuotientGroup.mk' (center (A ⧸ N))).comp (QuotientGroup.mk' N)).ker →*
      center (A ⧸ N) :=
    ((QuotientGroup.mk' N).comp (MonoidHom.ker _).subtype).codRestrict (center (A ⧸ N))
      fun x => by
        have hx := x.2
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
        exact (QuotientGroup.eq_one_iff _).mp hx
  have hfg : g.ker ≤ (inclusion hNk).range := by
    intro x hx
    have hx' : QuotientGroup.mk' N (x : A) = 1 := congrArg Subtype.val hx
    exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp hx'⟩, rfl⟩
  exact Group.isSolvable_of_ker_le_range (inclusion hNk) g hfg

theorem nonempty_equiv_statedSU_of_lieModel {Q : Type} [Group Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSU 3 3 1) :
    ∃ (F : Type) (_ : Field F), Nat.card F = 9 ∧ Nonempty (Q ≃* StatedSU 3 3 F) := by
  rcases hQ with ⟨-, -, F, _, _, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hF9 : Nat.card F = 9 := by rw [hF]; norm_num
    exact ⟨F, inferInstance, hF9, ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq
      (statedScalars_subgroupOf_statedSU_eq_bot hF9)).trans QuotientGroup.quotientBot)⟩⟩
  all_goals exact absurd h0 (by norm_num)

theorem ker_mulEquiv_comp_mk {A X : Type*} [Group A] [Group X] (N : Subgroup A) [N.Normal]
    (e : A ⧸ N ≃* X) : (e.toMonoidHom.comp (QuotientGroup.mk' N)).ker = N := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem original_K_containing_perfect_normal_overgroups_have_five_model_rigidity
    {T L M : Subgroup G} (h : QTNQ T L M) {H A : Subgroup G}
    (hKTH : nqOriginalK T L ⊔ T ≤ H) (hAH : A ≤ H) (hAn : (A.subgroupOf H).Normal)
    (hAp : ⁅A, A⁆ = A) (hKA : nqOriginalK T L ≤ A) :
    IsEmpty (A ⧸ CFSG.pCore 2 A ≃* alternatingGroup (Fin 6)) ∧
      ¬ (Group.IsPerfect (A ⧸ CFSG.pCore 2 A) ∧ Nat.card (center (A ⧸ CFSG.pCore 2 A)) = 3 ∧
        Nonempty ((A ⧸ CFSG.pCore 2 A) ⧸ center (A ⧸ CFSG.pCore 2 A) ≃*
          alternatingGroup (Fin 6))) ∧
      ¬ CFSG.Blueprint.LieModel (A ⧸ CFSG.pCore 2 A) .PSU 3 3 1 ∧
      ((Nonempty (A ⧸ CFSG.pCore 2 A ≃* alternatingGroup (Fin 5)) ∨
          CFSG.Blueprint.LieModel (A ⧸ CFSG.pCore 2 A) .PSL 3 2 1) →
        A = nqOriginalK T L ∧ pCoreOf 2 A = pCoreOf 2 (nqOriginalK T L) ∧ A ≤ M ∧
          H ≤ normalizer (nqOriginalK T L : Set G)) ∧
      (QT13Five (A ⧸ CFSG.pCore 2 A) →
        A = nqOriginalK T L ∧ A ≤ M ∧ H ≤ normalizer (nqOriginalK T L : Set G)) ∧
      (¬ A ≤ M → ¬ QT13Five (A ⧸ CFSG.pCore 2 A)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsol : Group.IsSolvable (CFSG.pCore 2 A) := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := A)).isNilpotent
    infer_instance
  have hA6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card]
    decide
  have hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have h6 : IsEmpty (A ⧸ CFSG.pCore 2 A ≃* alternatingGroup (Fin 6)) := ⟨fun e => by
    have : Group.IsSolvable (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 A))).ker := by
      rw [ker_mulEquiv_comp_mk]
      exact hsol
    exact false_of_surjective_three_sixty h hKTH hAH hAn hKA hA6card
      (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 A)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))⟩
  have h36 : ¬ (Group.IsPerfect (A ⧸ CFSG.pCore 2 A) ∧
      Nat.card (center (A ⧸ CFSG.pCore 2 A)) = 3 ∧
      Nonempty ((A ⧸ CFSG.pCore 2 A) ⧸ center (A ⧸ CFSG.pCore 2 A) ≃*
        alternatingGroup (Fin 6))) := by
    rintro ⟨-, -, ⟨e⟩⟩
    have : Group.IsSolvable (e.toMonoidHom.comp ((QuotientGroup.mk'
        (center (A ⧸ CFSG.pCore 2 A))).comp (QuotientGroup.mk' (CFSG.pCore 2 A)))).ker := by
      have hk : (e.toMonoidHom.comp ((QuotientGroup.mk' (center (A ⧸ CFSG.pCore 2 A))).comp
          (QuotientGroup.mk' (CFSG.pCore 2 A)))).ker =
          ((QuotientGroup.mk' (center (A ⧸ CFSG.pCore 2 A))).comp
            (QuotientGroup.mk' (CFSG.pCore 2 A))).ker := by
        ext x
        rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.map_eq_one_iff]
      rw [hk]
      exact isSolvable_ker_comp_center _
    exact false_of_surjective_three_sixty h hKTH hAH hAn hKA hA6card
      (e.toMonoidHom.comp ((QuotientGroup.mk' (center (A ⧸ CFSG.pCore 2 A))).comp
        (QuotientGroup.mk' (CFSG.pCore 2 A))))
      (e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)))
  have hU : ¬ CFSG.Blueprint.LieModel (A ⧸ CFSG.pCore 2 A) .PSU 3 3 1 := by
    intro hL
    obtain ⟨F, _, hF, ⟨e⟩⟩ := nonempty_equiv_statedSU_of_lieModel hL
    have : Group.IsSolvable (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 A))).ker := by
      rw [ker_mulEquiv_comp_mk]
      exact hsol
    exact false_of_surjective_SU33 h hKTH hAH hAn hKA hF
      (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 A)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hsmall : (Nonempty (A ⧸ CFSG.pCore 2 A ≃* alternatingGroup (Fin 5)) ∨
      CFSG.Blueprint.LieModel (A ⧸ CFSG.pCore 2 A) .PSL 3 2 1) → A = nqOriginalK T L := by
    rintro (he | hL)
    · obtain ⟨e⟩ := he
      have hA5card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup]
        simp [Nat.card_eq_fintype_card]
        decide
      refine eq_original_K_of_surjective h hKTH hAH hAn hAp hKA _ (ker_mulEquiv_comp_mk _ e) ?_
      intro s hs hs5 hsd
      rw [hA5card] at hsd ⊢
      rw [show (60 : ℕ) = 2 ^ 2 * 3 ^ 1 * 5 by norm_num] at hsd
      rw [prime_eq_of_dvd_two_three hs hs5 Nat.prime_five hsd]
      norm_num
    · obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 hL
      refine eq_original_K_of_surjective h hKTH hAH hAn hAp hKA _ (ker_mulEquiv_comp_mk _ e) ?_
      intro s hs hs5 hsd
      rw [CFSG.LieType.SteinbergBR.AutGL32.card_GL32] at hsd ⊢
      rw [show (168 : ℕ) = 2 ^ 3 * 3 ^ 1 * 7 by norm_num] at hsd
      rw [prime_eq_of_dvd_two_three hs hs5 (by norm_num) hsd]
      norm_num
  have hconc : (Nonempty (A ⧸ CFSG.pCore 2 A ≃* alternatingGroup (Fin 5)) ∨
      CFSG.Blueprint.LieModel (A ⧸ CFSG.pCore 2 A) .PSL 3 2 1) →
      A = nqOriginalK T L ∧ pCoreOf 2 A = pCoreOf 2 (nqOriginalK T L) ∧ A ≤ M ∧
        H ≤ normalizer (nqOriginalK T L : Set G) := by
    intro hm
    have hAK := hsmall hm
    obtain ⟨hKL, -⟩ := original_K_quotient_facts h
    have hHA : H ≤ normalizer (A : Set G) := (normal_subgroupOf_iff_le_normalizer hAH).mp hAn
    refine ⟨hAK, by rw [hAK], hAK ▸ hKL.trans h.l_le, ?_⟩
    rw [← hAK]
    exact hHA
  have h5 : QT13Five (A ⧸ CFSG.pCore 2 A) →
      A = nqOriginalK T L ∧ A ≤ M ∧ H ≤ normalizer (nqOriginalK T L : Set G) := by
    rintro (hm | hm | he | hm | hm)
    · obtain ⟨h1, -, h2, h3⟩ := hconc (Or.inl hm)
      exact ⟨h1, h2, h3⟩
    · obtain ⟨h1, -, h2, h3⟩ := hconc (Or.inr hm)
      exact ⟨h1, h2, h3⟩
    · obtain ⟨e⟩ := he
      exact (h6.false e).elim
    · exact (h36 hm).elim
    · exact (hU hm).elim
  exact ⟨h6, h36, hU, hconc, h5, fun hAM hm => hAM (h5 hm).2.1⟩

end CFSG.Quasithin.H13.NQBlock

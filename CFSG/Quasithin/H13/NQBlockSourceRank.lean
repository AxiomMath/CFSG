module

public import CFSG.Quasithin.H13.NQBlockResidualSupplement
public import CFSG.Quasithin.H13.NQTermIsotypicPair
public import CFSG.Quasithin.EmptyFaithful.S146D1
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.LieType.SteinbergBRTwoRankBound
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open
open scoped commutatorElement

theorem pRank_le_of_injective_hom {p : ℕ} [hp : Fact p.Prime] {Q P : Type*} [Group Q]
    [Group P] [Finite Q] [Finite P] (f : Q →* P) (hf : Function.Injective f) :
    CFSG.pRank p Q ≤ CFSG.pRank p P := by
  apply CFSG.LieType.SteinbergBR.pRank_le_of_card_le hp.out.one_lt
  intro E hE
  obtain ⟨n, hn⟩ := (CFSG.IsElementaryAbelian.isPGroup p ↥E).exists_card_eq
  have h1 : n ≤ CFSG.pRank p P :=
    CFSG.LieType.SteinbergBR.le_pRank_of_card hp.out.one_lt (E.map f)
      (CFSG.IsElementaryAbelian.map f) (by rw [Subgroup.card_map_of_injective hf, hn])
  rw [hn]
  exact Nat.pow_le_pow_right hp.out.pos h1

theorem two_le_pRank_of_not_isCyclic {p : ℕ} [hp : Fact p.Prime] {Q : Type} [Group Q]
    [Finite Q] (hexp : ∀ x : Q, x ^ p = 1) (hnc : ¬ IsCyclic Q) : 2 ≤ CFSG.pRank p Q := by
  classical
  have hQ : IsPGroup p Q := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  have : Nontrivial Q := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hnc isCyclic_of_subsingleton
  have := hQ.center_nontrivial
  obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : center Q)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨x, hx⟩ : ∃ x : Q, x ∉ zpowers z := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hnc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨z, eq_top_iff.mpr fun g _ => h g⟩)
  have hx1 : x ≠ 1 := fun h => hx (h ▸ one_mem _)
  have hzo : orderOf z = p := orderOf_eq_prime (hexp z) hz1'
  have hxo : orderOf x = p := orderOf_eq_prime (hexp x) hx1
  have hzC : zpowers z ≤ center Q := (zpowers_le (H := center Q)).mpr hzc
  have hinf : zpowers z ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyz, hyx⟩ := mem_inf.mp hy
    by_contra hy1
    rw [mem_bot] at hy1
    have hyo : orderOf y = p := orderOf_eq_prime (hexp y) hy1
    have hle : zpowers y ≤ zpowers x := (zpowers_le (H := zpowers x)).mpr hyx
    have heq : zpowers y = zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hxo])
    exact hx ((zpowers_le (H := zpowers z)).mpr hyz (heq ▸ mem_zpowers x))
  have h := NQTerm.add_le_pRank_of_commute hp.out (A := zpowers z) (B := zpowers x)
    (fun a ha b hb => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
      exact Commute.zpow_zpow_self z i j) (fun a _ => hexp a)
    (fun a ha b hb => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
      exact Commute.zpow_zpow_self x i j)
    (fun a _ => hexp a) (fun a ha b _ => ((mem_center_iff.mp (hzC ha)) b).symm) hinf
    (a := 1) (b := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
    (by rw [Nat.card_zpowers, hxo, pow_one])
  omega

theorem three_dvd_half_order {s : ℕ} (hs : s.Prime) (hs5 : 5 ≤ s) :
    3 ∣ s * (s ^ 2 - 1) / 2 := by
  have h3 : ¬ 3 ∣ s := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hs).mp h
    omega
  have h2 : ¬ 2 ∣ s := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hs).mp h
    omega
  have hs6 : s % 6 = 1 ∨ s % 6 = 5 := by omega
  have hsq : s ^ 2 % 6 = 1 := by
    rw [Nat.pow_mod]
    rcases hs6 with h | h <;> rw [h]
  have hpos : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨m, hm⟩ : 6 ∣ s ^ 2 - 1 := by omega
  rw [hm, show s * (6 * m) = 2 * (3 * (s * m)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  exact dvd_mul_right 3 _

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCore_iff_mem_pCoreOf {B : Subgroup G} (b : ↥B) :
    b ∈ CFSG.pCore 2 ↥B ↔ (b : G) ∈ pCoreOf 2 B := (CFSG.mem_openPCoreOf_iff b).symm

theorem pRank_three_le_one_of_commuting_simple {K Y H : Subgroup G} (hKH : K ≤ H) (hYH : Y ≤ H)
    (hH3 : CFSG.pRank 3 ↥H ≤ 2) (hKn : K ≤ normalizer (Y : Set G))
    (hYK : Y ≤ normalizer (K : Set G))
    (hYc : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 K)
    (hKY : ⁅K, Y⁆ ≤ pCoreOf 2 Y)
    (hcen : ∀ k ∈ K, (∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 K) → k ∈ pCoreOf 2 K)
    {k₀ : G} (hk₀ : k₀ ∈ K) (hk₀3 : k₀ ^ 3 ∈ pCoreOf 2 K) (hk₀Q : k₀ ∉ pCoreOf 2 K) :
    CFSG.pRank 3 (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp1 : 1 < 3 := by norm_num
  set B := K ⊔ Y with hBdef
  have hKB : K ≤ B := le_sup_left
  have hYB : Y ≤ B := le_sup_right
  have hBH : B ≤ H := sup_le hKH hYH
  set O := pCoreOf 2 B with hOdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B
  have hBO : B ≤ normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B
  have hBK : B ≤ normalizer (K : Set G) := sup_le le_normalizer hYK
  have hBY : B ≤ normalizer (Y : Set G) := sup_le hKn le_normalizer
  have hQKO : pCoreOf 2 K ≤ O := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKB)
    (hBK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hqYO : pCoreOf 2 Y ≤ O := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYB)
    (hBY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  have hKO : K ⊓ O ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => mem_normalizer_inf (hBK (hKB hg)) (hBO (hKB hg))) (hO2.to_le inf_le_right)
  have hOc : ∀ o ∈ O, ∀ k ∈ K, o * k * o⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
    intro o ho k hk
    refine hKO (mem_inf.mpr ⟨K.mul_mem ((mem_normalizer_iff.mp
      (hBK (CFSG.LieType.BorelTits.pCoreOf_le 2 B ho)) k).mp hk) (K.inv_mem hk), ?_⟩)
    have e : o * k * o⁻¹ * k⁻¹ = o * (k * o⁻¹ * k⁻¹) := by group
    rw [e]
    exact O.mul_mem ho ((mem_normalizer_iff.mp (hBO (hKB hk)) _).mp (O.inv_mem ho))
  have hYOc : ∀ y ∈ Y, ∀ o ∈ O, ∀ k ∈ K,
      (y * o) * k * (y * o)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
    intro y hy o ho k hk
    have e : (y * o) * k * (y * o)⁻¹ * k⁻¹ =
        y * (o * k * o⁻¹ * k⁻¹) * y⁻¹ * (y * k * y⁻¹ * k⁻¹) := by group
    rw [e]
    have hyQ : y ∈ normalizer (pCoreOf 2 K : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hYK hy)
    exact mul_mem ((mem_normalizer_iff.mp hyQ _).mp (hOc o ho k hk)) (hYc y hy k hk)
  have hmk_eq : ∀ a b : ↥B, (QuotientGroup.mk a : ↥B ⧸ CFSG.pCore 2 ↥B) = QuotientGroup.mk b ↔
      ((a⁻¹ * b : ↥B) : G) ∈ O := by
    intro a b
    rw [QuotientGroup.eq, mem_pCore_iff_mem_pCoreOf]
  have hYle : CFSG.pCore 2 ↥Y ≤ (CFSG.pCore 2 ↥B).comap (Subgroup.inclusion hYB) := by
    intro y hy
    rw [mem_comap, mem_pCore_iff_mem_pCoreOf]
    rw [mem_pCore_iff_mem_pCoreOf] at hy
    exact hqYO hy
  let φ : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* (↥B ⧸ CFSG.pCore 2 ↥B) :=
    QuotientGroup.map _ _ (Subgroup.inclusion hYB) hYle
  have hφ_mk : ∀ y : ↥Y, φ (QuotientGroup.mk y) = QuotientGroup.mk (Subgroup.inclusion hYB y) :=
    fun _ => rfl
  have hYO : Y ⊓ O ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => mem_normalizer_inf (le_normalizer hg) (hBO (hYB hg))) (hO2.to_le inf_le_right)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective u
    rw [hφ_mk, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at hu
    rw [QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
    exact hYO (mem_inf.mpr ⟨y.2, hu⟩)
  set kb : ↥B ⧸ CFSG.pCore 2 ↥B := QuotientGroup.mk (⟨k₀, hKB hk₀⟩ : ↥B) with hkbdef
  have hkb3 : kb ^ 3 = 1 := by
    rw [hkbdef, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
    exact hQKO hk₀3
  have hkb1 : kb ≠ 1 := by
    intro h1
    rw [hkbdef, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at h1
    exact hk₀Q (hcen k₀ hk₀ fun k hk => hOc k₀ h1 k hk)
  have hkbo : orderOf kb = 3 := orderOf_eq_prime hkb3 hkb1
  have hkc : ∀ b ∈ φ.range, kb * b = b * kb := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective u
    rw [hφ_mk, hkbdef, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmk_eq]
    have hc1 : ⁅(y : G)⁻¹, k₀⁻¹⁆ ∈ ⁅K, Y⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (Y.inv_mem y.2) (K.inv_mem hk₀)
    change (k₀ * (y : G))⁻¹ * ((y : G) * k₀) ∈ O
    have e : (k₀ * (y : G))⁻¹ * ((y : G) * k₀) = ⁅(y : G)⁻¹, k₀⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact hqYO (hKY hc1)
  have hc : ∀ a ∈ zpowers kb, ∀ b ∈ φ.range, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    exact Commute.zpow_left (hkc b hb) n
  have hinf : zpowers kb ⊓ φ.range = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, u, hu⟩ := mem_inf.mp hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx1
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective u
    rw [hφ_mk, hkbdef, ← QuotientGroup.mk_zpow, hmk_eq] at hu
    have ho : (y : G)⁻¹ * k₀ ^ n ∈ O := hu
    have hk : k₀ ^ n = (y : G) * ((y : G)⁻¹ * k₀ ^ n) := by group
    have hcent : ∀ k' ∈ K, k₀ ^ n * k' * (k₀ ^ n)⁻¹ * k'⁻¹ ∈ pCoreOf 2 K := by
      intro k' hk'
      rw [hk]
      exact hYOc y y.2 _ ho k' hk'
    have hkn := hcen _ (K.zpow_mem hk₀ n) hcent
    rw [mem_bot, hkbdef, ← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff,
      mem_pCore_iff_mem_pCoreOf]
    exact hQKO hkn
  have hBb : CFSG.pRank 3 (↥B ⧸ CFSG.pCore 2 ↥B) ≤ 2 := by
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three]
    · exact (pRank_le_of_injective_hom (Subgroup.inclusion hBH)
        (Subgroup.inclusion_injective hBH)).trans hH3
    · obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).exists_card_eq
      rw [hn]
      intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
  have hK3 : 1 ≤ CFSG.Open.pRank 3 (zpowers kb) := by
    refine CFSG.SectionRank.le_pRank hp1 le_rfl ⟨inferInstance, fun x hx => ?_⟩ (k := 1) ?_
    · obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hkb3, one_zpow]
    · rw [Nat.card_zpowers, hkbo, pow_one]
  have hsum := CFSG.Quasithin.pRank_add_le_pRank_sup Nat.prime_three hc hinf
  have hmono : CFSG.Open.pRank 3 (zpowers kb ⊔ φ.range) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (↥B ⧸ CFSG.pCore 2 ↥B)) :=
    CFSG.SectionRank.pRank_mono hp1 le_top
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at hmono
  have hYr : CFSG.Open.pRank 3 φ.range ≤ 1 := by omega
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  calc CFSG.Open.pRank 3 (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) ≤
        CFSG.Open.pRank 3 ((⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)).map φ) :=
      CFSG.SectionRank.pRank_le_map hp1 φ hφinj ⊤
    _ = CFSG.Open.pRank 3 φ.range := by rw [MonoidHom.range_eq_map]
    _ ≤ 1 := hYr

end CFSG.Quasithin.H13.NQBlock

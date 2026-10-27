module

public import CFSG.Quasithin.H13.A6S1372L74p
public import CFSG.Quasithin.H13.A6S1372L74a
public import CFSG.Quasithin.H13.A6S1372L76B

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L74

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem quot_comm_cube {K : Subgroup G} (hexp : ∀ k ∈ K, k ^ 3 ∈ pCoreOf 2 K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 K) :
    (∀ a b : ↥K ⧸ CFSG.pCore 2 ↥K, a * b = b * a) ∧ ∀ a : ↥K ⧸ CFSG.pCore 2 ↥K, a ^ 3 = 1 := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
        have h1 : a * b * a⁻¹ * b⁻¹ ∈ CFSG.pCore 2 ↥K :=
          (mem_pCoreOf_iff (a * b * a⁻¹ * b⁻¹)).1 (hcomm a a.2 b b.2)
        rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥K)] at h1
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
        exact h1
  · induction x using QuotientGroup.induction_on with
    | H a =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact (mem_pCoreOf_iff (a ^ 3)).1 (by simpa using hexp a a.2)

theorem le_pRank_of_card {K : Subgroup G} (hexp : ∀ k ∈ K, k ^ 3 ∈ pCoreOf 2 K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 K) {n : ℕ}
    (hn : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 ^ n) : n ≤ CFSG.Open.pRank 3 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hc, h3⟩ := quot_comm_cube hexp hcomm
  have hE : IsElemAbelian 3 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    ⟨⟨⟨fun a b => Subtype.ext (hc a b)⟩⟩, fun y _ => h3 y⟩
  have h1 : n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE (by rw [Subgroup.card_top, hn])
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥K)).exists_card_eq
    rw [hj]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have h2 := A6L76B.pRank_map_le (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) hker ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup K] at h2
  omega

theorem three_le_pRank_of_comm {K : Subgroup G} (hexp : ∀ k ∈ K, k ^ 3 ∈ pCoreOf 2 K)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 K)
    (h9 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 9) {x : G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx3 : x ^ 3 = 1) (hxK : x ∉ K)
    (hxc : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    3 ≤ CFSG.Open.pRank 3 (K ⊔ Subgroup.zpowers x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hc, h3⟩ := quot_comm_cube hexp hcomm
  have hnt : Nontrivial (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h9]; norm_num)
  obtain ⟨a, ha1⟩ := exists_ne (1 : ↥K ⧸ CFSG.pCore 2 ↥K)
  obtain ⟨b, hb⟩ : ∃ b, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have hle : (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) ≤ Subgroup.zpowers a := fun y _ => h y
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_top, h9, Nat.card_zpowers] at h1
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) (h3 a)
    omega
  obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨k₂, rfl⟩ := QuotientGroup.mk_surjective b
  set Y := K ⊔ Subgroup.zpowers x with hY
  have hOY : pCoreOf 2 K ≤ Y := (pCoreOf_le 2 K).trans le_sup_left
  have hYO : Y ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    sup_le (le_normalizer_pCoreOf 2 K)
      (Subgroup.zpowers_le.2 (normalizer_le_normalizer_pCoreOf 2 K hxN))
  have hN : ((pCoreOf 2 K).subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOY).mpr hYO
  have hmk : ∀ c d : ↥Y, (QuotientGroup.mk c : ↥Y ⧸ (pCoreOf 2 K).subgroupOf Y) =
      QuotientGroup.mk d ↔ (c : G)⁻¹ * d ∈ pCoreOf 2 K := by
    intro c d
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  have hmk1 : ∀ c : ↥Y, (QuotientGroup.mk c : ↥Y ⧸ (pCoreOf 2 K).subgroupOf Y) = 1 ↔
      (c : G) ∈ pCoreOf 2 K := by
    intro c
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcommY : ∀ c d : ↥Y, (c * d * c⁻¹ * d⁻¹ : G) ∈ pCoreOf 2 K →
      Commute (QuotientGroup.mk c : ↥Y ⧸ (pCoreOf 2 K).subgroupOf Y) (QuotientGroup.mk d) := by
    intro c d h
    have h1 := (hmk1 (c * d * c⁻¹ * d⁻¹)).2 (by simpa using h)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  set y₁ : ↥Y := ⟨k₁, Subgroup.mem_sup_left k₁.2⟩ with hy₁
  set y₂ : ↥Y := ⟨k₂, Subgroup.mem_sup_left k₂.2⟩ with hy₂
  set y₃ : ↥Y := ⟨x, Subgroup.mem_sup_right (Subgroup.mem_zpowers x)⟩ with hy₃
  have hcube : ∀ c : ↥K, (QuotientGroup.mk (⟨c, Subgroup.mem_sup_left c.2⟩ : ↥Y) :
      ↥Y ⧸ (pCoreOf 2 K).subgroupOf Y) ^ 3 = 1 := by
    intro c
    rw [← QuotientGroup.mk_pow, hmk1]
    simpa using hexp c c.2
  have hxk : ∀ c : ↥K, ((c : G) * x * (c : G)⁻¹ * x⁻¹) ∈ pCoreOf 2 K := by
    intro c
    have h := (pCoreOf 2 K).inv_mem (hxc c c.2)
    have e : (x * c * x⁻¹ * (c : G)⁻¹)⁻¹ = (c : G) * x * (c : G)⁻¹ * x⁻¹ := by group
    rwa [e] at h
  have key := CFSG.SectionRank.ClassicalEven.three_le_pRank_of_gens
    (G := ↥Y ⧸ (pCoreOf 2 K).subgroupOf Y)
    (x := QuotientGroup.mk y₁) (y := QuotientGroup.mk y₂) (z := QuotientGroup.mk y₃)
    (hcube k₁) (hcube k₂)
    (by
      rw [← QuotientGroup.mk_pow, show y₃ ^ 3 = 1 from Subtype.ext (by simpa using hx3)]
      rfl)
    (hcommY y₁ y₂ (by simpa using hcomm k₁ k₁.2 k₂ k₂.2))
    (hcommY y₁ y₃ (by simpa using hxk k₁)) (hcommY y₂ y₃ (by simpa using hxk k₂))
    (fun h => ha1 (by
      rw [hmk1] at h
      rw [QuotientGroup.eq_one_iff]
      exact (mem_pCoreOf_iff k₁).1 h))
    (fun n h => hb (by
      rw [← QuotientGroup.mk_pow, hmk] at h
      refine ⟨n, ?_⟩
      show ((k₁ : ↥K ⧸ CFSG.pCore 2 ↥K)) ^ (n : ℤ) = (k₂ : ↥K ⧸ CFSG.pCore 2 ↥K)
      rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq]
      exact (mem_pCoreOf_iff _).1 (by simpa using h)))
    (fun n m h => hxK (by
      rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, hmk] at h
      have h1 : ((k₁ : G) ^ n * (k₂ : G) ^ m)⁻¹ * x ∈ K := (pCoreOf_le 2 K) (by simpa using h)
      have e : x = ((k₁ : G) ^ n * (k₂ : G) ^ m) * (((k₁ : G) ^ n * (k₂ : G) ^ m)⁻¹ * x) := by
        group
      rw [e]
      exact K.mul_mem (K.mul_mem (K.pow_mem k₁.2 n) (K.pow_mem k₂.2 m)) h1))
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf Y)).ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨j, hj⟩ := ((pCoreOf_isPGroup 2 K).comap_subtype (K := Y)).exists_card_eq
    have e : Nat.card ↥((pCoreOf 2 K).subgroupOf Y) = 2 ^ j := hj
    rw [e]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    omega
  have h2 := A6L76B.pRank_map_le (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf Y)) hker ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y] at h2
  omega

end A6L74

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem exists_L1_not_mem (hhat : ¬ IsHatA6 L)
    {K : Subgroup G} (hL1K : ¬ S.L1 ≤ K) : ∃ x ∈ S.L1, x ^ 3 = 1 ∧ x ∉ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  apply hL1K
  show oTwoRes (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) ≤ K
  rw [oTwoRes, Subgroup.closure_le]
  rintro x ⟨hx, m, hm, hxm⟩
  have hxL1 : x ∈ S.L1 := Subgroup.subset_closure ⟨hx, m, hm, hxm⟩
  refine hno x hxL1 ?_
  obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, S.cube_mem_pCoreOf_L1 hhat hxL1⟩
  have ha' : (x ^ 3) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hm' : (x ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
  exact A6L19.eq_one_of_odd_of_two hm hm' ha'

section Odd

variable {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H)
  (hHK : H ≤ Subgroup.normalizer (K : Set G))
include hH hKH hHK

theorem card_eq_three (h1227 : U3.Stmt13_2_2_7)
    (hhat : ¬ IsHatA6 L) (hB : ¬ H13.IsA6Block L)
    (hKU : ¬ K ≤ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G)) (hL1K : ¬ S.L1 ≤ K)
    (hexp : ∀ k ∈ K, k ^ 3 ∈ pCoreOf 2 K)
    (hcomm : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ pCoreOf 2 K)
    (hCK : K ⊓ Subgroup.centralizer
      (twoReducedProduct (K ⊔ pCoreOf 2 (S.L1 ⊔ T)) : Set G) = pCoreOf 2 K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, h3⟩ := A6L74.quot_comm_cube hexp hcomm
  have hP : IsPGroup 3 (↥K ⧸ CFSG.pCore 2 ↥K) := fun y => ⟨1, by rw [pow_one]; exact h3 y⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hH2 : CFSG.Open.pRank 3 H ≤ 2 :=
    pRank_le_two_of_pCoreOf_ne_bot S.h13.qtke hH.1.2 Nat.prime_three (by norm_num)
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n
    ·
      exfalso
      apply hKU
      have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
        le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
          (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
      have hsub : Subsingleton (↥K ⧸ CFSG.pCore 2 ↥K) :=
        (Nat.card_eq_one_iff_unique.mp (by rw [hn, pow_zero])).1
      intro k hk
      have h1 : (QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := Subsingleton.elim _ _
      rw [QuotientGroup.eq_one_iff] at h1
      have hkO := (A6L74.mem_pCoreOf_iff ⟨k, hk⟩).2 h1
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.mp hu.2 k (hOQ hkO)).symm
    · rw [hn, pow_one]
  rcases Nat.lt_or_ge n 3 with hlt3 | hge3
  ·
    exfalso
    have hn2 : n = 2 := by omega
    rw [hn2] at hn
    have h9 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 9 := by rw [hn]; norm_num
    obtain ⟨x, hxL, hx3, hxK⟩ := exists_L1_not_mem hhat hL1K
    have hxc := comm_L1_of_card_nine hH hKH hHK h1227 hhat hB hKM hexp hcomm hCK h9 hxL hx3
    have hL1N : S.L1 ≤ Subgroup.normalizer (K : Set G) := (le_sup_left.trans hH.1.1).trans hHK
    have h1 := A6L74.three_le_pRank_of_comm hexp hcomm h9 (hL1N hxL) hx3 hxK hxc
    have hYH : K ⊔ Subgroup.zpowers x ≤ H :=
      sup_le hKH (Subgroup.zpowers_le.2 ((le_sup_left.trans hH.1.1) hxL))
    have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hYH
    omega
  ·
    exfalso
    have h1 := A6L74.le_pRank_of_card hexp hcomm hn
    have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hKH
    omega

end Odd

end Setting4

theorem lem1374OneOdd_of (h1227 : U3.Stmt13_2_2_7)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) : Lem1374OneOdd := by
  intro G _ _ T L V S hNS _ hhat H hH hab hB p hp hp2 K hKH hHK _ _ hKU hKU' hKM hL1K hexp
    hcomm _
  have hCK := Setting4.inf_centralizer_R2_eq hH hKH hHK hNS h13315 h1356two hab hKU'
  have h3 := Setting4.eq_three hH hKH hHK h1227 hhat hB hKM hp hp2 hexp hcomm hCK
  subst h3
  exact ⟨rfl, Setting4.card_eq_three hH hKH hHK h1227 hhat hB hKU hKM hL1K hexp hcomm hCK⟩

end CFSG.Quasithin.H13.A6

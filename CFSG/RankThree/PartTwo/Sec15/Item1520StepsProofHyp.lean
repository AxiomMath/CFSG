module

public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofTools
import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)
open scoped Pointwise

namespace Proof1520

theorem two_pow_mod_nine_cases {f : ℕ} (h3 : ¬ 3 ∣ f) :
    (f % 2 = 1 ∧ (2 ^ f % 9 = 2 ∨ 2 ^ f % 9 = 5)) ∨
      (f % 2 = 0 ∧ (2 ^ f % 9 = 4 ∨ 2 ^ f % 9 = 7)) := by
  have h6 : 2 ^ f % 9 = 2 ^ (f % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod f 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have : f % 6 = 1 ∨ f % 6 = 2 ∨ f % 6 = 4 ∨ f % 6 = 5 := by omega
  rcases this with h | h | h | h <;> rw [h6, h]
  · exact Or.inl ⟨by omega, by norm_num⟩
  · exact Or.inr ⟨by omega, by norm_num⟩
  · exact Or.inr ⟨by omega, by norm_num⟩
  · exact Or.inl ⟨by omega, by norm_num⟩

theorem not_nine_dvd_card_projSL {f : ℕ} (hf : 1 ≤ f) (hodd : f % 2 = 1) (h3 : ¬ 3 ∣ f) :
    ¬ 9 ∣ Nat.card (projSL 3 (GaloisField 2 f)) := by
  have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 f)
  rw [GaloisField.card 2 f (Nat.one_le_iff_ne_zero.mp hf)] at hc
  have hq9 : 2 ^ f % 9 = 2 ∨ 2 ^ f % 9 = 5 := by
    rcases two_pow_mod_nine_cases h3 with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · omega
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hg : Nat.gcd 3 (2 ^ f - 1) = 1 := by
    have : (2 ^ f - 1) % 3 = 1 := by omega
    rw [Nat.gcd_rec, this, Nat.gcd_one_left]
  rw [hg, mul_one] at hc
  rw [hc]
  intro h9
  have h0 := (ZMod.natCast_eq_zero_iff _ 9).mpr h9
  have hq2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq3 : 1 ≤ (2 ^ f) ^ 3 := Nat.one_le_pow _ _ (by omega)
  push_cast [Nat.cast_sub hq2, Nat.cast_sub hq3] at h0
  have hqz : ((2 ^ f : ℕ) : ZMod 9) = ((2 ^ f % 9 : ℕ) : ZMod 9) := (ZMod.natCast_mod _ 9).symm
  push_cast at hqz
  rcases hq9 with h | h <;> rw [hqz, h] at h0 <;> revert h0 <;> decide

theorem not_nine_dvd_card_projSU {f : ℕ} (hf : 1 ≤ f) (heven : f % 2 = 0) (h3 : ¬ 3 ∣ f) :
    ¬ 9 ∣ Nat.card (projSU 3 2 f) := by
  have hc := KFacts.KS14.card_projSU_three_mul_gcd 2 f hf
  have hq9 : 2 ^ f % 9 = 4 ∨ 2 ^ f % 9 = 7 := by
    rcases two_pow_mod_nine_cases h3 with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact h
  have hg : Nat.gcd 3 (2 ^ f + 1) = 1 := by
    have : (2 ^ f + 1) % 3 = 2 := by omega
    rw [Nat.gcd_rec, this]
    norm_num
  rw [hg, mul_one] at hc
  rw [hc]
  intro h9
  have h0 := (ZMod.natCast_eq_zero_iff _ 9).mpr h9
  have hq2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  push_cast [Nat.cast_sub hq2] at h0
  have hqz : ((2 ^ f : ℕ) : ZMod 9) = ((2 ^ f % 9 : ℕ) : ZMod 9) := (ZMod.natCast_mod _ 9).symm
  push_cast at hqz
  rcases hq9 with h | h <;> rw [hqz, h] at h0 <;> revert h0 <;> decide

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem center_eq_bot_of_mulEquiv {X T : Type*} [Group X] [Group T] (φ : X ≃* T)
    (h : Subgroup.center T = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hφ : φ x ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨y, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, hx y]
  rw [h, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hφ
  rw [hφ]
  exact one_mem _

omit [Finite G] in
theorem mem_pCore_two_iff {Y : Subgroup G} {y : ↥Y} :
    y ∈ CFSG.pCore 2 ↥Y ↔ (y : G) ∈ CFSG.Open.pCoreOf 2 Y := (CFSG.mem_openPCoreOf_iff y).symm

theorem eq_one_of_mem_pCoreOf_two {Y : Subgroup G} {x : G}
    (hx : x ∈ CFSG.Open.pCoreOf 2 Y) (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk')
    (orderOf_dvd_of_pow_eq_one hx3))

omit [Finite G] in
theorem conj_mul_inv_mem_of_eq_sup {L Y : Subgroup G} {g : G}
    (hYeq : Y = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y) (hgL : ∀ l ∈ L, g * l = l * g)
    (hgY : g ∈ Subgroup.normalizer (Y : Set G)) {y : G} (hy : y ∈ Y) :
    g * y * g⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
  have hYN : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hgO : g ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hgY
  have hy' : y ∈ (((L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := by
    rw [← hYeq]
    exact hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (inf_le_right.trans hYN)] at hy'
  obtain ⟨k, hk, o, ho, rfl⟩ := hy'
  have hgk : g * k * g⁻¹ = k := by rw [hgL k hk.1, mul_inv_cancel_right]
  have hgo : g * o * g⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
    (Subgroup.mem_normalizer_iff.mp hgO o).mp ho
  have h1 : g * o * g⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
    Subgroup.mul_mem _ hgo (Subgroup.inv_mem _ ho)
  have h2 := (Subgroup.mem_normalizer_iff.mp (hYN hk.2) _).mp h1
  have : g * (k * o) * g⁻¹ * (k * o)⁻¹ = k * (g * o * g⁻¹ * o⁻¹) * k⁻¹ := by
    calc g * (k * o) * g⁻¹ * (k * o)⁻¹ = (g * k * g⁻¹) * (g * o * g⁻¹) * o⁻¹ * k⁻¹ := by group
      _ = k * (g * o * g⁻¹ * o⁻¹) * k⁻¹ := by rw [hgk]; group
  rw [this]
  exact h2

theorem eq_sup_of_card_inf {A Y : Subgroup G} {c : G} (hA : Nat.card A = 27) (hcA : c ∈ A)
    (h9 : Nat.card ↥(A ⊓ Y) = 9) (hcY : c ∉ Y) : A = Subgroup.zpowers c ⊔ (A ⊓ Y) := by
  set S := Subgroup.zpowers c ⊔ (A ⊓ Y) with hSdef
  have hSA : S ≤ A := sup_le (Subgroup.zpowers_le.mpr hcA) inf_le_left
  have hBS : A ⊓ Y ≤ S := le_sup_right
  have h1 : 9 ∣ Nat.card S := h9 ▸ Subgroup.card_dvd_of_le hBS
  have h2 : Nat.card S ∣ 3 ^ 3 := by
    rw [show 3 ^ 3 = 27 by norm_num, ← hA]
    exact Subgroup.card_dvd_of_le hSA
  have h3 : Nat.card S ≠ 9 := by
    intro h
    have : A ⊓ Y = S := Subgroup.eq_of_le_of_card_ge hBS (by rw [h, h9])
    exact hcY (this ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c) : c ∈ A ⊓ Y).2
  obtain ⟨k, hk, hSk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  have h27 : Nat.card S = 27 := by
    interval_cases k <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hSA (by rw [h27, hA])).symm

omit [Finite G] in
theorem nonempty_mulEquiv_sup_prod {X : Type*} [Group X] (S T : Subgroup X)
    (hcomm : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) (hdisj : S ⊓ T = ⊥) :
    Nonempty (↥(S ⊔ T) ≃* ↥S × ↥T) := by
  let f : ↥S × ↥T →* X := MonoidHom.noncommCoprod S.subtype T.subtype
    (fun s t => (hcomm s s.2 t t.2))
  have hfapp : ∀ s : S, ∀ t : T, f (s, t) = (s : X) * t := fun s t => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨s, t⟩ h
    have h' : (s : X) * t = 1 := by rw [← hfapp]; exact h
    have hs : (s : X) = (t : X)⁻¹ := eq_inv_of_mul_eq_one_left h'
    have hs1 : (s : X) ∈ S ⊓ T := ⟨s.2, by rw [hs]; exact T.inv_mem t.2⟩
    rw [hdisj, Subgroup.mem_bot] at hs1
    have ht1 : (t : X) = 1 := by
      rw [hs1, one_mul] at h'
      exact h'
    exact Prod.ext (Subtype.ext hs1) (Subtype.ext ht1)
  have hrange : f.range = S ⊔ T := by
    apply le_antisymm
    · rintro _ ⟨⟨s, t⟩, rfl⟩
      rw [hfapp]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left s.2) (Subgroup.mem_sup_right t.2)
    · refine sup_le (fun s hs => ⟨(⟨s, hs⟩, 1), by simp [hfapp]⟩)
        (fun t ht => ⟨(1, ⟨t, ht⟩), by simp [hfapp]⟩)
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem nonempty_quot_equiv_prod {A Y : Subgroup G} {c : G}
    (hYA : A ≤ Subgroup.normalizer (Y : Set G)) (hcA : c ∈ A) (hc3 : orderOf c = 3)
    (hcY : c ∉ Y) (hAle : A ≤ Subgroup.zpowers c ⊔ Y)
    (htriv : ∀ k : ℤ, ∀ y ∈ Y, c ^ k * y * (c ^ k)⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y) :
    letI := kerAO2_normal hYA
    Nonempty (↥(A ⊔ Y) ⧸ kerAO2 A Y ≃* Multiplicative (ZMod 3) × (↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
  have := kerAO2_normal hYA
  set B : Subgroup G := A ⊔ Y with hB
  set π : ↥B →* ↥B ⧸ kerAO2 A Y := QuotientGroup.mk' (kerAO2 A Y) with hπ
  have hYB : Y ≤ B := le_sup_right
  have hcB : c ∈ B := Subgroup.mem_sup_left hcA
  have hO2Y : CFSG.Open.pCoreOf 2 Y ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYN : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hπeq : ∀ a b : ↥B, π a = π b ↔ (a : G)⁻¹ * b ∈ CFSG.Open.pCoreOf 2 Y := by
    intro a b
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rfl
  have hcpow : ∀ k : ℤ, c ^ k ∈ Y → c ^ k = 1 := by
    intro k hk
    set D : Subgroup G := Subgroup.zpowers c ⊓ Y with hD
    have hD3 : Nat.card ↥D ∣ 3 := by
      rw [← hc3, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hkD : c ^ k ∈ D := ⟨Subgroup.zpow_mem_zpowers c k, hk⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hD3 with h1 | h3
    · rw [Subgroup.eq_bot_of_card_eq D h1] at hkD
      exact hkD
    · exfalso
      have hDc : D = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hc3, h3])
      have hcD : c ∈ D := hDc ▸ Subgroup.mem_zpowers c
      exact hcY hcD.2
  set γ : ↥B := ⟨c, hcB⟩ with hγ
  set S : Subgroup (↥B ⧸ kerAO2 A Y) := Subgroup.zpowers (π γ) with hS
  set T : Subgroup (↥B ⧸ kerAO2 A Y) := (Y.subgroupOf B).map π with hT
  have hπγk : ∀ k : ℤ, ((γ ^ k : ↥B) : G) = c ^ k := fun k => by simp [hγ]
  have hST : S ⊔ T = ⊤ := by
    have htop : (Subgroup.zpowers c).subgroupOf B ⊔ Y.subgroupOf B = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (Subgroup.zpowers_le.mpr hcB) hYB]
      have hBeq : Subgroup.zpowers c ⊔ Y = B :=
        le_antisymm (sup_le (Subgroup.zpowers_le.mpr hcB) hYB)
          (sup_le hAle le_sup_right)
      rw [hBeq, Subgroup.subgroupOf_self]
    have hle : ((Subgroup.zpowers c).subgroupOf B).map π ≤ S := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
      have : x = γ ^ k := Subtype.ext (by rw [hπγk, hk])
      rw [this, map_zpow]
      exact Subgroup.zpow_mem_zpowers _ k
    rw [eq_top_iff, ← Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _), ← htop,
      Subgroup.map_sup]
    exact sup_le_sup_right hle T
  have hSTb : S ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxS, hxT⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxS
    obtain ⟨y, hy, hyx⟩ := hxT
    rw [← map_zpow] at hyx
    have h1 := (hπeq _ _).mp hyx
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    have h2 : (y : G)⁻¹ * c ^ k ∈ Y := by
      rw [← hπγk]
      exact hO2Y h1
    have hck : c ^ k ∈ Y := by
      have := Y.mul_mem hyY h2
      rwa [mul_inv_cancel_left] at this
    rw [Subgroup.mem_bot, ← map_zpow]
    have hγk : γ ^ k = 1 := Subtype.ext (by rw [hπγk, hcpow k hck]; rfl)
    rw [hγk, map_one]
  have hcomm : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s := by
    intro s hs t ht
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    obtain ⟨y, hy, rfl⟩ := ht
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
    rw [← map_zpow, ← map_mul, ← map_mul, hπeq]
    simp only [Subgroup.coe_mul, hπγk]
    have h1 := htriv (-k) (y : G) hyY
    have h2 := (Subgroup.mem_normalizer_iff.mp (hYN (Y.inv_mem hyY)) _).mp h1
    have : (y : G)⁻¹ * (c ^ (-k) * (y : G) * (c ^ (-k))⁻¹ * (y : G)⁻¹) * (y : G)⁻¹⁻¹ =
        (c ^ k * (y : G))⁻¹ * ((y : G) * c ^ k) := by group
    rw [this] at h2
    exact h2
  have hγ1 : π γ ≠ 1 := by
    intro h1
    have h2 : π γ = π 1 := by rw [h1, map_one]
    have h3 := (hπeq _ _).mp h2
    simp only [hγ, OneMemClass.coe_one, mul_one] at h3
    exact hcY (hO2Y (by simpa using Subgroup.inv_mem _ h3))
  have hγ3 : π γ ^ 3 = 1 := by
    rw [← map_pow]
    have : γ ^ 3 = 1 := Subtype.ext (by simp [hγ, ← hc3, pow_orderOf_eq_one])
    rw [this, map_one]
  have hS3 : Nat.card ↥S = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [hS, Nat.card_zpowers, orderOf_eq_prime hγ3 hγ1]
  have eS : ↥S ≃* Multiplicative (ZMod 3) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc : IsCyclic ↥S := isCyclic_of_prime_card hS3
    have e := zmodCyclicMulEquiv hcyc
    rw [hS3] at e
    exact e.symm
  set ρ : ↥Y →* ↥B ⧸ kerAO2 A Y := π.comp (Subgroup.inclusion hYB) with hρ
  have hρr : ρ.range = T := by
    rw [hρ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hρk : ρ.ker = CFSG.pCore 2 ↥Y := by
    ext y
    rw [MonoidHom.mem_ker, mem_pCore_two_iff]
    have : ρ y = π 1 ↔ _ := hπeq (Subgroup.inclusion hYB y) 1
    rw [map_one] at this
    rw [this]
    simp only [Subgroup.coe_inclusion, OneMemClass.coe_one, mul_one]
    exact ⟨fun h => by simpa using Subgroup.inv_mem _ h, fun h => Subgroup.inv_mem _ h⟩
  have eT : ↥T ≃* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    ((MulEquiv.subgroupCongr hρr).symm.trans (QuotientGroup.quotientKerEquivRange ρ).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hρk)
  obtain ⟨e1⟩ := nonempty_mulEquiv_sup_prod S T hcomm hSTb
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hST.symm)).trans
    (e1.trans (MulEquiv.prodCongr eS eT))⟩

theorem quot_facts_of_nine_dvd (h1518 : Step1518R) (h138 : Item138N) {A : Subgroup G} {c : G}
    {L Y : Subgroup G} (h : Sec15R G A c L) (hctx : Ctx1514 A (lB A) c L Y)
    (hYA : A ≤ Subgroup.normalizer (Y : Set G))
    (h9Y : 9 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y)) :
    ∃ f : ℕ, 1 ≤ f ∧ ¬ 3 ∣ f ∧ 2 < 2 ^ f ∧ Sec4.IsoLThreePi (↥Y ⧸ CFSG.pCore 2 ↥Y) 2 f ∧
      (∀ k : ℤ, ∀ y ∈ Y, c ^ k * y * (c ^ k)⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y) ∧ c ∉ Y := by
  obtain ⟨r, e, hr, he, hiso, hprod, hYeq, ⟨n', f, hf1, hef, hYiso⟩, -⟩ := hctx.concl1515
  have hr2 : r = 2 := h1518 G A c L h Y hctx r e he hiso
  subst hr2
  have h9e := not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC he hiso hprod
  have h3e : ¬ 3 ∣ e := fun h3 => h9e (two_pow_mod_nine_of_three_dvd h3)
  have h3f : ¬ 3 ∣ f := fun h3 => h3e (hef ▸ Dvd.dvd.mul_left h3 n')
  have hD := h.toSec13Data
  have hc3 : orderOf c = 3 := hD.orderOf_eq
  have hcA : c ∈ A := hD.mem_A
  have hsign : Sec4.IsoLThreePi (↥Y ⧸ CFSG.pCore 2 ↥Y) 2 f ∧ 2 < 2 ^ f := by
    rcases hYiso with ⟨⟨φ⟩⟩ | ⟨hq2, ⟨φ⟩⟩
    · have hmod : 2 ^ f % 3 = 1 := by
        rcases two_pow_mod_nine_cases h3f with ⟨hodd, -⟩ | ⟨heven, -⟩
        · exact absurd (Nat.card_congr φ.toEquiv ▸ h9Y) (not_nine_dvd_card_projSL hf1 hodd h3f)
        · exact Proof1514.two_pow_mod_three_of_even (Nat.even_iff.mpr heven)
      refine ⟨Or.inl ⟨hmod, ⟨φ⟩⟩, ?_⟩
      have heven : f % 2 = 0 := by
        by_contra hodd
        rw [Proof1514.two_pow_mod_three_of_odd (Nat.odd_iff.mpr (by omega))] at hmod
        omega
      have : 2 ^ 1 < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
      simpa using this
    · have hmod : 2 ^ f % 3 = 2 := by
        rcases two_pow_mod_nine_cases h3f with ⟨hodd, -⟩ | ⟨heven, -⟩
        · exact Proof1514.two_pow_mod_three_of_odd (Nat.odd_iff.mpr hodd)
        · exact absurd (Nat.card_congr φ.toEquiv ▸ h9Y) (not_nine_dvd_card_projSU hf1 heven h3f)
      exact ⟨Or.inr ⟨hmod, ⟨φ⟩⟩, hq2⟩
  obtain ⟨hpi, hq2⟩ := hsign
  have hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ := by
    rcases hpi with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSL 2 f hf1 hq).2
    · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSU 2 f hf1 hq hq2).2
  have hcL : ∀ l ∈ L, c * l = l * c := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)).symm
  have htriv : ∀ k : ℤ, ∀ y ∈ Y, c ^ k * y * (c ^ k)⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y :=
    fun k y hy => conj_mul_inv_mem_of_eq_sup hYeq
      (fun l hl => (Commute.zpow_left (hcL l hl) k).eq) (Subgroup.zpow_mem _ (hYA hcA) k) hy
  have hcY : c ∉ Y := by
    intro hcY
    have hmem : (QuotientGroup.mk (⟨c, hcY⟩ : ↥Y) : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈
        Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_pCore_two_iff]
      have h1 := htriv (-1) ((y : G)⁻¹) (Y.inv_mem y.2)
      have : c ^ (-1 : ℤ) * (y : G)⁻¹ * (c ^ (-1 : ℤ))⁻¹ * (y : G)⁻¹⁻¹ =
          ((y : G) * c)⁻¹ * (c * (y : G)) := by group
      rw [this] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact h1
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff, mem_pCore_two_iff] at hmem
    have hc31 : c ^ 3 = 1 := by rw [← hc3, pow_orderOf_eq_one]
    exact hD.ne_one (eq_one_of_mem_pCoreOf_two hmem hc31)
  exact ⟨f, hf1, h3f, hq2, hpi, htriv, hcY⟩

theorem nine_dvd_card_quot_of_card_inf {A Y : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h9 : Nat.card ↥(A ⊓ Y) = 9) :
    9 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  set ρ : ↥(A ⊓ Y) →* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion inf_le_right) with hρ
  have hρi : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_pCore_two_iff] at ha
    exact Subtype.ext (eq_one_of_mem_pCoreOf_two ha (hA.2 _ a.2.1))
  rw [← h9, Nat.card_congr (MonoidHom.ofInjective hρi).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

end Proof1520

open Proof1520

theorem step1522Hyp_of (h1518 : Step1518R) (h138 : Item138N) (hmeet : Step1522HypMeet)
    (hl34 : Step1522HypNotL34) : Step1522Hyp := by
  intro G _ _ A c L h Y hctx p P hP hYA
  have hD := h.toSec13Data
  have h9 := hmeet G A c L h Y hctx p P hP
  obtain ⟨f, hf1, h3f, hq2, hpi, htriv, hcY⟩ := quot_facts_of_nine_dvd h1518 h138 h hctx hYA
    (nine_dvd_card_quot_of_card_inf hD.isElemAbelian h9)
  have hf2 : f ≠ 2 := by
    rintro rfl
    rcases hpi with ⟨-, ⟨φ⟩⟩ | ⟨hq, -⟩
    · exact (hl34 G A c L h Y hctx p P hP).false φ
    · norm_num at hq
  have hf1' : f ≠ 1 := by
    rintro rfl
    norm_num at hq2
  have hf3 : f ≠ 3 := fun h3 => h3f ⟨1, by omega⟩
  have hf4 : 4 ≤ f := by omega
  have hAeq := eq_sup_of_card_inf hD.card_eq hD.mem_A h9 hcY
  have hAle : A ≤ Subgroup.zpowers c ⊔ Y := by
    rw [hAeq]
    exact sup_le le_sup_left (inf_le_right.trans le_sup_right)
  obtain ⟨φ⟩ := nonempty_quot_equiv_prod hYA hD.mem_A hD.orderOf_eq hcY hAle htriv
  exact ⟨f, hf4, ↥Y ⧸ CFSG.pCore 2 ↥Y, inferInstance, hpi, ⟨φ⟩⟩

end CFSG.RankThree.PartTwo.Sec15

module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.H13.L32A767g

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem exists_mem_coset_centralizer {p : ℕ} [Fact p.Prime] {A N : Subgroup G}
    (hA : IsPGroup p A) (hN : ¬ p ∣ Nat.card N) (hAN : A ≤ Subgroup.normalizer (N : Set G))
    {b : G} (hb : ∀ a ∈ A, b⁻¹ * (a * b * a⁻¹) ∈ N) :
    ∃ n ∈ N, ∀ a ∈ A, a * (b * n) * a⁻¹ = b * n := by
  have hmem : ∀ a ∈ A, ∀ g : G, b⁻¹ * g ∈ N → b⁻¹ * (a * g * a⁻¹) ∈ N := by
    intro a ha g hg
    have h2 : a * (b⁻¹ * g) * a⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hAN ha) _).mp hg
    have := mul_mem (hb a ha) h2
    rwa [show b⁻¹ * (a * b * a⁻¹) * (a * (b⁻¹ * g) * a⁻¹) = b⁻¹ * (a * g * a⁻¹) by group] at this
  let _ : MulAction ↥A {g : G // b⁻¹ * g ∈ N} :=
    { smul := fun a g => ⟨a * g * (a : G)⁻¹, hmem a a.2 g g.2⟩
      one_smul := fun g => Subtype.ext
        (show ((1 : ↥A) : G) * (g : G) * ((1 : ↥A) : G)⁻¹ = g by simp)
      mul_smul := fun a a' g => Subtype.ext
        (show ((a * a' : ↥A) : G) * (g : G) * ((a * a' : ↥A) : G)⁻¹ =
          (a : G) * ((a' : G) * g * (a' : G)⁻¹) * (a : G)⁻¹ by simp [mul_assoc]) }
  have hcard : Nat.card {g : G // b⁻¹ * g ∈ N} = Nat.card N :=
    Nat.card_congr ⟨fun g => ⟨b⁻¹ * g, g.2⟩, fun n => ⟨b * n, by simp⟩,
      fun g => Subtype.ext (by simp), fun n => Subtype.ext (by simp)⟩
  obtain ⟨⟨g, hg⟩, hfix⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card _ (by rwa [hcard])
  refine ⟨b⁻¹ * g, hg, fun a ha => ?_⟩
  have := congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hfix) ⟨a, ha⟩)
  rw [mul_inv_cancel_left]
  exact this

omit [Finite G] in
theorem isElemAbelian_zpowers_of_pow {p : ℕ} {x : G} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem false_of_commute_three (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    {x₁ x₂ : G} (h₁ : x₁ ∈ dK T V) (h₂ : x₂ ∈ dK T V) (ho₁ : orderOf x₁ = 3)
    (ho₂ : orderOf x₂ = 3) (hc : Commute x₁ x₂) (hx : x₂ ∉ Subgroup.zpowers x₁) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE1 : IsElemAbelian 3 (Subgroup.zpowers x₁) :=
    isElemAbelian_zpowers_of_pow (ho₁ ▸ pow_orderOf_eq_one x₁)
  obtain ⟨hE9, hE9c⟩ := exists_elemAbelian_sup_zpowers hE1 ho₂
    (fun e he => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
      exact hc.zpow_left k) hx
  have hED : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ≤ dK T V :=
    sup_le (Subgroup.zpowers_le.mpr h₁) (Subgroup.zpowers_le.mpr h₂)
  have hcard9 : Nat.card ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) = 3 ^ 2 := by
    rw [hE9c, Nat.card_zpowers, ho₁]
    norm_num
  obtain ⟨-, π, -, hπs, hπk, -⟩ := isL24Section_u0 h hMod h63
  obtain ⟨A, hA3⟩ := exists_prime_orderOf_dvd_card' (G := SL(2, F4)) 3
    (by rw [card_sl24]; norm_num)
  have hA1 : A ≠ 1 := fun e => by rw [e, orderOf_one] at hA3; norm_num at hA3
  have hA3' : A ^ 3 = 1 := hA3 ▸ pow_orderOf_eq_one A
  obtain ⟨k₀, hk₀⟩ := hπs A
  have hON : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 (kz T V)) := by
    obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 (kz T V)).exists_card_eq
    rw [hm]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hKO : kz T V ≤ Subgroup.normalizer (pCoreOf 2 (kz T V) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hEO : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ≤
      Subgroup.normalizer (pCoreOf 2 (kz T V) : Set G) := fun e he =>
    normalizer_le_normalizer_pCoreOf 2 _ (hED he).1
  have hE3 : IsPGroup 3 ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) := fun g =>
    ⟨1, Subtype.ext (by simpa using hE9.2 g g.2)⟩
  have hb : ∀ a ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂,
      (k₀ : G)⁻¹ * (a * k₀ * a⁻¹) ∈ pCoreOf 2 (kz T V) := by
    intro a ha
    have h1 : a * k₀ * a⁻¹ * (k₀ : G)⁻¹ ∈ pCoreOf 2 (kz T V) := (hED ha).2 k₀ k₀.2
    have h2 := (Subgroup.mem_normalizer_iff.mp (hKO (inv_mem k₀.2)) _).mp h1
    rwa [show (k₀ : G)⁻¹ * (a * k₀ * a⁻¹ * (k₀ : G)⁻¹) * (k₀ : G)⁻¹⁻¹ =
      (k₀ : G)⁻¹ * (a * k₀ * a⁻¹) by group] at h2
  obtain ⟨n, hnO, hfix⟩ := exists_mem_coset_centralizer hE3 hON hEO hb
  have hnK : n ∈ kz T V := pCoreOf_le 2 _ hnO
  set k₁ : ↥(kz T V) := k₀ * ⟨n, hnK⟩ with hk₁
  have hπk₁ : π k₁ = A := by
    have : π ⟨n, hnK⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hπk, Subgroup.mem_subgroupOf]
      exact hnO
    rw [hk₁, map_mul, this, mul_one, hk₀]
  have h3ker : k₁ ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hπk₁, hA3']
  rw [hπk, Subgroup.mem_subgroupOf] at h3ker
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 (kz T V)) ⟨_, h3ker⟩
  have hm' : ((k₁ : G) ^ 3) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  set k₂ : ↥(kz T V) := k₁ ^ 4 ^ m with hk₂
  have hpow : ∀ j : ℕ, A ^ 4 ^ j = A := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_mul, ih, show 4 = 3 + 1 by rfl, pow_succ, hA3', one_mul]
  have hπk₂ : π k₂ = A := by rw [hk₂, map_pow, hπk₁, hpow]
  have hk₂3 : (k₂ : G) ^ 3 = 1 := by
    rw [hk₂, SubgroupClass.coe_pow, ← pow_mul, mul_comm, pow_mul,
      show (4 : ℕ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num, pow_mul, hm', one_pow]
  have hk₂1 : (k₂ : G) ≠ 1 := by
    intro e
    apply hA1
    rw [← hπk₂, show k₂ = 1 from Subtype.ext e, map_one]
  have hk₂o : orderOf (k₂ : G) = 3 := orderOf_eq_prime hk₂3 hk₂1
  have hcomm : ∀ e ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, Commute e (k₂ : G) := by
    intro e he
    have h1 : Commute e (k₁ : G) := by
      have := hfix e he
      have hc1 : (k₁ : G) = (k₀ : G) * n := rfl
      rw [hc1]
      show e * ((k₀ : G) * n) = (k₀ : G) * n * e
      calc e * ((k₀ : G) * n) = e * ((k₀ : G) * n) * e⁻¹ * e := by group
        _ = (k₀ : G) * n * e := by rw [this]
    rw [hk₂, SubgroupClass.coe_pow]
    exact h1.pow_right _
  have hk₂E : (k₂ : G) ∉ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ := by
    intro hk
    have hO := mem_pCoreOf_of_mem_dK h hMod h63 k₂.2 (hED hk)
    apply hA1
    rw [← hπk₂, ← MonoidHom.mem_ker, hπk, Subgroup.mem_subgroupOf]
    exact hO
  obtain ⟨hE27, hE27c⟩ := exists_elemAbelian_sup_zpowers hE9 hk₂o hcomm hk₂E
  have hE27N : Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers (k₂ : G) ≤
      Subgroup.normalizer (pCoreOf 2 (kz T V) : Set G) :=
    sup_le hEO (Subgroup.zpowers_le.mpr (hKO k₂.2))
  have hle := CFSG.Quasithin.le_pRank Nat.prime_three hE27N hE27 (k := 3)
    (by rw [hE27c, hcard9]; norm_num)
  have h2loc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (kz T V) : Set G)) :=
    ⟨pCoreOf 2 (kz T V), pCoreOf_kz_ne_bot h hMod h63, pCoreOf_isPGroup 2 _, rfl⟩
  have hle2 := A1b.pRank_le_evenRank Nat.prime_three (by norm_num) h2loc
  have he : evenRank G ≤ 2 := h.fsu.qtke.2.2
  omega

end CFSG.Quasithin.H13.L32A

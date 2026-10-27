module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Frame

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace FA5

namespace Frame

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G} (F : Frame L1 L2 S D X)
include F

theorem exists_mul_of_pow_five {y : G} (hy : y ∈ L1) (hy5 : y ^ 5 ∈ pCoreOf 2 L1) :
    ∃ x ∈ X, ∃ o ∈ pCoreOf 2 L1, y = x * o := by
  let π : ↥L1 →* oTwoQuot ↥L1 := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L1)
  have hker : ∀ l : ↥L1, π l = 1 ↔ (l : G) ∈ pCoreOf 2 L1 := by
    intro l
    show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L1) l = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact F1.mem_pCore_iff_coe l
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hXcyc : IsCyclic X := isCyclic_of_prime_card (p := 5) F.X_card
  obtain ⟨⟨x0, hx0⟩, hgen⟩ := hXcyc.exists_generator
  have hx0L : x0 ∈ L1 := F.X_le hx0
  have hx05 : x0 ^ 5 = 1 := by
    have := pow_card_eq_one' (G := ↥X) (x := ⟨x0, hx0⟩)
    rw [F.X_card] at this
    simpa using congrArg Subtype.val this
  have hx01 : x0 ≠ 1 := by
    intro h
    have hall : ∀ x : X, x = 1 := by
      intro x
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen x)
      rw [← hj]
      have : (⟨x0, hx0⟩ : ↥X) = 1 := Subtype.ext h
      rw [this, one_zpow]
    have : Nat.card X = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => by rw [hall a, hall b]⟩,
      ⟨1⟩⟩
    rw [F.X_card] at this
    omega
  set ξ : oTwoQuot ↥L1 := π ⟨x0, hx0L⟩ with hξdef
  have hξ5 : ξ ^ 5 = 1 := by
    rw [hξdef, ← map_pow]
    have : (⟨x0, hx0L⟩ : ↥L1) ^ 5 = 1 := Subtype.ext (by simpa using hx05)
    rw [this, map_one]
  have hξ1 : ξ ≠ 1 := by
    intro h
    have h2 : x0 ∈ pCoreOf 2 L1 := (hker ⟨x0, hx0L⟩).mp h
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L1) ⟨x0, h2⟩
    have hk' : x0 ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hg : Nat.gcd (2 ^ k) 5 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hk', hx05⟩
    rw [hg, pow_one] at this
    exact hx01 this
  have hξord : orderOf ξ = 5 := orderOf_eq_prime hξ5 hξ1
  have hcardR : Nat.card (oTwoQuot ↥L1) = 10 ∨ Nat.card (oTwoQuot ↥L1) = 20 := F.card1
  have hf5 : (Nat.card (oTwoQuot ↥L1)).factorization 5 = 1 := by
    rcases hcardR with h | h <;> rw [h] <;> decide +kernel
  let P0 : Sylow 5 (oTwoQuot ↥L1) :=
    Sylow.ofCard (Subgroup.zpowers ξ) (by rw [Nat.card_zpowers, hξord, hf5]; norm_num)
  have hP0 : (P0 : Subgroup (oTwoQuot ↥L1)) = Subgroup.zpowers ξ := Sylow.coe_ofCard _ _
  have hn1 : Nat.card (Sylow 5 (oTwoQuot ↥L1)) = 1 := by
    have hmod := card_sylow_modEq_one 5 (oTwoQuot ↥L1)
    have hdvd := Sylow.card_dvd_index P0
    have hmul := Subgroup.card_mul_index (P0 : Subgroup (oTwoQuot ↥L1))
    have hc5 : Nat.card (P0 : Subgroup (oTwoQuot ↥L1)) = 5 := by
      rw [hP0, Nat.card_zpowers, hξord]
    rw [hc5] at hmul
    have hidx : (P0 : Subgroup (oTwoQuot ↥L1)).index ≤ 4 := by
      rcases hcardR with h | h <;> omega
    have hidx0 : 0 < (P0 : Subgroup (oTwoQuot ↥L1)).index := by
      rcases hcardR with h | h <;> omega
    have hle : Nat.card (Sylow 5 (oTwoQuot ↥L1)) ≤ 4 := (Nat.le_of_dvd hidx0 hdvd).trans hidx
    have hpos : 0 < Nat.card (Sylow 5 (oTwoQuot ↥L1)) := Nat.card_pos
    have hmod' : Nat.card (Sylow 5 (oTwoQuot ↥L1)) % 5 = 1 := hmod
    omega
  have hsub : Subsingleton (Sylow 5 (oTwoQuot ↥L1)) := (Nat.card_eq_one_iff_unique.mp hn1).1
  set ybar : oTwoQuot ↥L1 := π ⟨y, hy⟩ with hybar
  have hy5' : ybar ^ 5 = 1 := by
    rw [hybar, ← map_pow]
    exact (hker _).mpr (by simpa using hy5)
  have hpg : IsPGroup 5 (Subgroup.zpowers ybar) := by
    have hdvd : orderOf ybar ∣ 5 := orderOf_dvd_of_pow_eq_one hy5'
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  obtain ⟨P', hP'⟩ := hpg.exists_le_sylow
  have hPeq : P' = P0 := Subsingleton.elim _ _
  have hmem : ybar ∈ Subgroup.zpowers ξ := by
    rw [← hP0, ← hPeq]
    exact hP' (Subgroup.mem_zpowers ybar)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hxj : x0 ^ j ∈ X := X.zpow_mem hx0 j
  have hxjL : x0 ^ j ∈ L1 := F.X_le hxj
  have hπ : π ⟨x0 ^ j, hxjL⟩ = ybar := by
    have : (⟨x0 ^ j, hxjL⟩ : ↥L1) = ⟨x0, hx0L⟩ ^ j := Subtype.ext (by simp)
    rw [this, map_zpow]
    exact hj
  refine ⟨x0 ^ j, hxj, (x0 ^ j)⁻¹ * y, ?_, by group⟩
  have h1 : π (⟨x0 ^ j, hxjL⟩⁻¹ * ⟨y, hy⟩) = 1 := by
    rw [map_mul, map_inv, hπ, ← hybar, inv_mul_cancel]
  have := (hker _).mp h1
  simpa using this

theorem conj_mem_X_mul {b x : G} (hb : b ∈ bigB L1 L2 S) (hx : x ∈ X) :
    ∃ x' ∈ X, ∃ o ∈ pCoreOf 2 L1, b * x * b⁻¹ = x' * o := by
  have hxL : x ∈ L1 := F.X_le hx
  have hx5 : x ^ 5 = 1 := by
    have := pow_card_eq_one' (G := ↥X) (x := ⟨x, hx⟩)
    rw [F.X_card] at this
    simpa using congrArg Subtype.val this
  have hyL : b * x * b⁻¹ ∈ L1 :=
    (Subgroup.mem_normalizer_iff.mp (F.B_le_normalizer_L1 hb) x).mp hxL
  have hy5 : (b * x * b⁻¹) ^ 5 ∈ pCoreOf 2 L1 := by
    have : (b * x * b⁻¹) ^ 5 = 1 := by
      rw [conj_pow, hx5]
      group
    rw [this]
    exact (pCoreOf 2 L1).one_mem
  exact F.exists_mul_of_pow_five hyL hy5

end Frame

end FA5

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Quasithin

open CFSG.Open

theorem eq_one_of_pow_three_of_isPGroup_two {K : Type*} [Group K] {N : Subgroup K}
    (hN : IsPGroup 2 N) {x : K} (hx : x ∈ N) (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨j, hj⟩ := hN ⟨x, hx⟩
  have hj' : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have h2 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
  have h3 : orderOf x ∣ Nat.gcd 3 (2 ^ j) := Nat.dvd_gcd h1 h2
  have h4 : Nat.gcd 3 (2 ^ j) = 1 :=
    Nat.Coprime.pow_right j (by norm_num : Nat.Coprime 3 2)
  rw [h4] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem mem_of_zpow_mem_of_pow_three_mem {K : Type*} [Group K] (C : Subgroup K) {g : K}
    (hg3 : g ^ 3 ∈ C) {m : ℤ} (hm : g ^ m ∈ C) (h3 : ¬ (3 : ℤ) ∣ m) : g ∈ C := by
  have hmod : m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hq : m = 3 * (m / 3) + m % 3 := by omega
  have e1 : g ^ m = (g ^ 3) ^ (m / 3) * g ^ (m % 3) := by
    conv_lhs => rw [hq]
    rw [zpow_add, zpow_mul]
    simp
  have h1 : g ^ (m % 3) ∈ C := by
    have h2 : ((g ^ 3) ^ (m / 3))⁻¹ * g ^ m ∈ C :=
      C.mul_mem (C.inv_mem (C.zpow_mem hg3 _)) hm
    have e2 : ((g ^ 3) ^ (m / 3))⁻¹ * g ^ m = g ^ (m % 3) := by
      rw [e1]
      group
    rwa [e2] at h2
  rcases hmod with h | h
  · rw [h] at h1
    simpa using h1
  · rw [h] at h1
    have h2 : g ^ 3 * ((g ^ (2 : ℤ))⁻¹) ∈ C := C.mul_mem hg3 (C.inv_mem h1)
    have e3 : g ^ 3 * ((g ^ (2 : ℤ))⁻¹) = g := by group
    rwa [e3] at h2

theorem exists_injective_noncommCoprod_quotient {K : Type*} [Group K] (N : Subgroup K) [N.Normal]
    (hN : IsPGroup 2 N) {A : Type*} [Group A] (hAp : ∀ a : A, a ^ 3 = 1) (ι : A →* K)
    (hι : Function.Injective ι) (g : K) (hg3 : g ^ 3 ∈ N)
    (hcomm : ∀ a : A, ι a * g * (ι a)⁻¹ * g⁻¹ ∈ N)
    (hind : ∀ (a : A) (n : K), n ∈ N → ∀ m : ℤ, g ^ m = ι a * n → (3 : ℤ) ∣ m) :
    ∃ f : A × (Subgroup.zpowers (QuotientGroup.mk g : K ⧸ N)) →* K ⧸ N,
      Function.Injective f := by
  classical
  let mk : K →* K ⧸ N := QuotientGroup.mk' N
  let gb : K ⧸ N := mk g
  let fE : A →* K ⧸ N := mk.comp ι
  let fG : ↥(Subgroup.zpowers gb) →* K ⧸ N := (Subgroup.zpowers gb).subtype
  have hcommE : ∀ a : A, Commute (fE a) gb := by
    intro a
    have h1 := hcomm a
    have h2 : mk (ι a * g * (ι a)⁻¹ * g⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    show mk (ι a) * gb = gb * mk (ι a)
    calc mk (ι a) * gb = (mk (ι a) * gb * (mk (ι a))⁻¹ * gb⁻¹) * gb * mk (ι a) := by group
      _ = gb * mk (ι a) := by rw [h2]; group
  have hcommEG : ∀ (a : A) (c : ↥(Subgroup.zpowers gb)), Commute (fE a) (fG c) := by
    intro a c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp c.2
    show Commute (fE a) (c : K ⧸ N)
    rw [← hk]
    exact (hcommE a).zpow_right k
  have hgb3 : gb ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hg3
  refine ⟨MonoidHom.noncommCoprod fE fG hcommEG, ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨a, c⟩ hac
  rw [MonoidHom.mem_ker] at hac
  have hac' : fE a * fG c = 1 := hac
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp c.2
  have hk' : gb ^ k = fG c := hk
  have h3 : fE a = (fG c)⁻¹ := eq_inv_of_mul_eq_one_left hac'
  have h2 : (QuotientGroup.mk (ι a) : K ⧸ N) = (QuotientGroup.mk (g ^ (-k)) : K ⧸ N) := by
    have : (QuotientGroup.mk (g ^ (-k)) : K ⧸ N) = gb ^ (-k) := (map_zpow mk g (-k))
    rw [this, zpow_neg, hk']
    exact h3
  have h4 : (ι a)⁻¹ * g ^ (-k) ∈ N := QuotientGroup.eq.mp h2
  have h5 : g ^ (-k) = ι a * ((ι a)⁻¹ * g ^ (-k)) := by group
  have h6 : (3 : ℤ) ∣ -k := hind a _ h4 (-k) h5
  have h7 : (3 : ℤ) ∣ k := (dvd_neg).mp h6
  obtain ⟨j, hj⟩ := h7
  have h8 : gb ^ k = 1 := by
    rw [hj, zpow_mul]
    simp [hgb3]
  have hc1 : c = 1 := Subtype.ext (hk'.symm.trans h8)
  have h9 : (QuotientGroup.mk (ι a) : K ⧸ N) = 1 := by
    rw [h2]
    have : (QuotientGroup.mk (g ^ (-k)) : K ⧸ N) = gb ^ (-k) := (map_zpow mk g (-k))
    rw [this, zpow_neg, h8]
    simp
  have h10 : ι a ∈ N := (QuotientGroup.eq_one_iff _).mp h9
  have h11 : ι a = 1 :=
    eq_one_of_pow_three_of_isPGroup_two hN h10 (by rw [← map_pow, hAp, map_one])
  have ha1 : a = 1 := hι (by rw [h11, map_one])
  rw [Subgroup.mem_bot]
  exact Prod.ext ha1 hc1

theorem succ_le_pRank_quotient {K : Type} [Group K] [Finite K] (N : Subgroup K) [N.Normal]
    (hN : IsPGroup 2 N) {A : Type} [Group A] (hAc : ∀ a b : A, a * b = b * a)
    (hAp : ∀ a : A, a ^ 3 = 1) {r : ℕ} (hAcard : Nat.card A = 3 ^ r) (ι : A →* K)
    (hι : Function.Injective ι) (g : K) (hg3 : g ^ 3 ∈ N)
    (hcomm : ∀ a : A, ι a * g * (ι a)⁻¹ * g⁻¹ ∈ N)
    (hind : ∀ (a : A) (n : K), n ∈ N → ∀ m : ℤ, g ^ m = ι a * n → (3 : ℤ) ∣ m) :
    r + 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ N)) := by
  classical
  obtain ⟨f, hf⟩ := exists_injective_noncommCoprod_quotient N hN hAp ι hι g hg3 hcomm hind
  let gb : K ⧸ N := QuotientGroup.mk g
  have hgb3 : gb ^ 3 = 1 := by
    show (QuotientGroup.mk g : K ⧸ N) ^ 3 = 1
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hg3
  have hgb1 : gb ≠ 1 := by
    intro h1
    have h2 : g ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    have := hind 1 g h2 1 (by simp)
    omega
  have hord : orderOf gb = 3 := orderOf_eq_prime hgb3 hgb1
  have hcardz : Nat.card (Subgroup.zpowers gb) = 3 := by
    rw [Nat.card_zpowers, hord]
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num)
    (A := A × ↥(Subgroup.zpowers gb)) ?_ ?_ ?_ f hf (le_top)
  · intro a b
    refine Prod.ext (hAc _ _) ?_
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2.2
    apply Subtype.ext
    show (a.2 : K ⧸ N) * (b.2 : K ⧸ N) = (b.2 : K ⧸ N) * (a.2 : K ⧸ N)
    rw [← hi, ← hj]
    exact Commute.zpow_zpow_self gb i j
  · intro a
    refine Prod.ext (hAp _) ?_
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
    apply Subtype.ext
    show (a.2 : K ⧸ N) ^ 3 = 1
    rw [← hi]
    have e : (gb ^ i) ^ (3 : ℕ) = (gb ^ (3 : ℕ)) ^ i := by
      rw [← zpow_natCast, ← zpow_natCast gb 3, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [e, hgb3, one_zpow]
  · rw [Nat.card_prod, hAcard, hcardz, pow_succ]

end CFSG.Quasithin

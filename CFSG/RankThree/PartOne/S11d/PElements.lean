module

public import CFSG.RankThree.PGroups.PrimaryFactorization
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star

public section

namespace CFSG.RankThree.PartOne

open Subgroup

variable {G : Type*} [Group G]

theorem pElement_mul_of_commute {p : ℕ} (hp : p.Prime) {x y : G} (hxy : Commute x y)
    (hx : ∃ k : ℕ, orderOf x = p ^ k) (hy : ∃ k : ℕ, orderOf y = p ^ k) :
    ∃ k : ℕ, orderOf (x * y) = p ^ k := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  have h1 : x ^ (p ^ (a + b)) = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw [ha]
    exact pow_dvd_pow p (by omega)
  have h2 : y ^ (p ^ (a + b)) = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw [hb]
    exact pow_dvd_pow p (by omega)
  have h3 : (x * y) ^ (p ^ (a + b)) = 1 := by rw [hxy.mul_pow, h1, h2, one_mul]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one h3)
  exact ⟨k, hk⟩

theorem pElement_inv {p : ℕ} {x : G} (hx : ∃ k : ℕ, orderOf x = p ^ k) :
    ∃ k : ℕ, orderOf x⁻¹ = p ^ k := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [orderOf_inv, hk]⟩

theorem pElement_pow {p : ℕ} (hp : p.Prime) {x : G} (hx : ∃ k : ℕ, orderOf x = p ^ k) (n : ℕ) :
    ∃ k : ℕ, orderOf (x ^ n) = p ^ k := by
  obtain ⟨k, hk⟩ := hx
  have : orderOf (x ^ n) ∣ p ^ k := by
    rw [← hk]
    exact orderOf_pow_dvd _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 this
  exact ⟨j, hj⟩

theorem pElement_zpow {p : ℕ} (hp : p.Prime) {x : G} (hx : ∃ k : ℕ, orderOf x = p ^ k) (m : ℤ) :
    ∃ k : ℕ, orderOf (x ^ m) = p ^ k := by
  obtain ⟨k, hk⟩ := hx
  have h1 : (x ^ m) ^ (p ^ k) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hk, pow_orderOf_eq_one,
      one_zpow]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one h1)
  exact ⟨j, hj⟩

theorem eq_one_of_pPart_coprime {p : ℕ} (hp : p.Prime) {x : G} (h1 : ∃ k : ℕ, orderOf x = p ^ k)
    (h2 : Nat.Coprime (orderOf x) p) : x = 1 := by
  obtain ⟨k, hk⟩ := h1
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact orderOf_eq_one_iff.mp (by simpa using hk)
  · exfalso
    rw [hk] at h2
    have h3 : Nat.Coprime p p := Nat.Coprime.coprime_dvd_left (dvd_pow_self p hk0.ne') h2
    exact hp.one_lt.ne' (Nat.coprime_self p |>.mp h3)

theorem coprime_orderOf_mul {p : ℕ} {x y : G} (hxy : Commute x y) (hx : Nat.Coprime (orderOf x) p)
    (hy : Nat.Coprime (orderOf y) p) : Nat.Coprime (orderOf (x * y)) p :=
  (Nat.Coprime.mul_left hx hy).coprime_dvd_left
    (hxy.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))

theorem exists_pElement_decomp [Finite G] {p : ℕ} (hp : p.Prime) {L : Subgroup G}
    (hZ : ∀ x ∈ L, x ∈ centralizer (L : Set G) → Nat.Coprime (orderOf x) p) {ℓ z : G}
    (hℓ : ℓ ∈ L) (hz : z ∈ centralizer (L : Set G)) (hu : ∃ k : ℕ, orderOf (ℓ * z) = p ^ k) :
    ∃ ℓ' ∈ L, ∃ z' ∈ centralizer (L : Set G), ℓ * z = ℓ' * z' ∧
      (∃ k : ℕ, orderOf ℓ' = p ^ k) ∧ (∃ k : ℕ, orderOf z' = p ^ k) := by
  have hℓz : Commute ℓ z := mem_centralizer_iff.mp hz ℓ hℓ
  obtain ⟨k, hk⟩ := hu
  have h1 : ℓ ^ (p ^ k) * z ^ (p ^ k) = 1 := by
    rw [← hℓz.mul_pow, ← hk, pow_orderOf_eq_one]
  have hw0 : ℓ ^ (p ^ k) = (z ^ (p ^ k))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hw0L : ℓ ^ (p ^ k) ∈ L := L.pow_mem hℓ _
  have hw0C : ℓ ^ (p ^ k) ∈ centralizer (L : Set G) := by
    rw [hw0]
    exact inv_mem ((centralizer (L : Set G)).pow_mem hz _)
  have hw0c : Nat.Coprime (orderOf (ℓ ^ (p ^ k))) p := hZ _ hw0L hw0C
  have hℓfin : IsOfFinOrder ℓ := isOfFinOrder_of_finite ℓ
  obtain ⟨⟨⟨u, v⟩, ⟨huv, hvu, hu', hvfin, hvc⟩, -⟩, hmem⟩ :=
    CFSG.RankThree.PGroups.prime_primary_factorization hℓfin hp
  dsimp only at huv hvu hu' hvfin hvc
  obtain ⟨huℓ, hvℓ, -⟩ := hmem u v huv hvu hu' hvfin hvc
  have huv' : Commute u v := huv.trans hvu.symm
  have hsplit : ℓ ^ (p ^ k) = u ^ (p ^ k) * v ^ (p ^ k) := by
    calc ℓ ^ (p ^ k) = (u * v) ^ (p ^ k) := by rw [huv]
      _ = u ^ (p ^ k) * v ^ (p ^ k) := huv'.mul_pow _
  have hup : ∃ j : ℕ, orderOf (u ^ (p ^ k)) = p ^ j := pElement_pow hp hu' _
  have hvp : Nat.Coprime (orderOf (v ^ (p ^ k))) p :=
    Nat.Coprime.coprime_dvd_left (orderOf_pow_dvd _) hvc
  have hu1 : u ^ (p ^ k) = 1 := by
    have h2 : u ^ (p ^ k) = ℓ ^ (p ^ k) * (v ^ (p ^ k))⁻¹ := eq_mul_inv_of_mul_eq hsplit.symm
    refine eq_one_of_pPart_coprime hp hup ?_
    rw [h2]
    have hcom : Commute (ℓ ^ (p ^ k)) (v ^ (p ^ k))⁻¹ := by
      rw [hsplit]
      exact (((huv'.pow_pow _ _).mul_left (Commute.refl _)).inv_right)
    exact coprime_orderOf_mul hcom hw0c (by rwa [orderOf_inv])
  have hvv : ℓ ^ (p ^ k) = v ^ (p ^ k) := by rw [hsplit, hu1, one_mul]
  have hvC : v ∈ centralizer (L : Set G) := by
    have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (orderOf v : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_left k hvc.symm
    obtain ⟨x, y, hxy⟩ := hcop
    have hxy' : ((p ^ k : ℕ) : ℤ) * x + (orderOf v : ℤ) * y = 1 := by linarith
    have hv : v = (v ^ (p ^ k)) ^ x := by
      calc v = v ^ (1 : ℤ) := (zpow_one v).symm
        _ = v ^ (((p ^ k : ℕ) : ℤ) * x + (orderOf v : ℤ) * y) := by rw [hxy']
        _ = (v ^ (p ^ k)) ^ x := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, pow_orderOf_eq_one,
            one_zpow, mul_one]
    rw [hv, ← hvv]
    exact zpow_mem hw0C x
  have hℓ' : u ∈ L := (zpowers_le.mpr hℓ) huℓ
  refine ⟨u, hℓ', v * z, mul_mem hvC hz, ?_, hu', ?_⟩
  · rw [← huv, mul_assoc]
  · have hc : Commute u (ℓ * z) := by
      have h1 : Commute u ℓ := by
        rw [← huv]
        exact Commute.mul_right (Commute.refl u) huv'
      have h2 : Commute u z := by
        have hu_mem : u ∈ zpowers ℓ := huℓ
        obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hu_mem
        rw [← hm]
        exact hℓz.zpow_left m
      exact h1.mul_right h2
    have hz' : v * z = u⁻¹ * (ℓ * z) := by rw [← huv]; group
    rw [hz']
    exact pElement_mul_of_commute hp hc.inv_left (pElement_inv hu') ⟨k, hk⟩

end CFSG.RankThree.PartOne

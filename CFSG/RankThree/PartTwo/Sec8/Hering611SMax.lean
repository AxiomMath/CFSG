module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SGenA
public import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_of_fixed_coset {A X N : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A)
    (hNX : N ≤ X) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hN3 : ¬ 3 ∣ Nat.card N)
    {x : G} (hxX : x ∈ X) (hx3 : x ^ 3 ∈ N)
    (hxA : ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ N) :
    ∃ y ∈ A, y ∈ X ∧ y⁻¹ * x ∈ N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconj : ∀ c ∈ N, x⁻¹ * c * x ∈ N := fun c hc =>
    (Subgroup.mem_normalizer_iff''.mp (hXN hxX) c).mp hc
  have hy : ∀ b ∈ A, x⁻¹ * (b * x * b⁻¹) ∈ N := by
    intro b hb
    have h1 := hconj _ (hxA b hb)
    have h2 : x⁻¹ * (b * x * b⁻¹ * x⁻¹) * x = x⁻¹ * (b * x * b⁻¹) := by group
    rwa [h2] at h1
  obtain ⟨n, hnN, hfix⟩ := exists_fixed_mem_coset
    (CFSG.RankThree.PartTwo.Sec5.isPGroup_of_isElemAbelian hAe) hN3 hAN hy
  have hcommA : ∀ a ∈ A, Commute a (x * n) := fun a ha =>
    mul_inv_eq_iff_eq_mul.mp (hfix a ha)
  have hpow : ∀ e ∈ N, ∀ j : ℕ, (x ^ j)⁻¹ * (x * e) ^ j ∈ N := by
    intro e he j
    induction j with
    | zero => simp
    | succ j ih =>
      have e' : (x ^ (j + 1))⁻¹ * (x * e) ^ (j + 1)
          = (x⁻¹ * ((x ^ j)⁻¹ * (x * e) ^ j) * x) * e := by
        simp only [pow_succ, mul_inv_rev, mul_assoc]
      rw [e']
      exact N.mul_mem (hconj _ ih) he
  obtain ⟨r, s, hs3, hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (orderOf_pos (x * n)).ne' 3 (by norm_num)
  have hsq : s ^ 2 % 3 = 1 := by
    have h12 : s % 3 = 1 ∨ s % 3 = 2 := by omega
    rcases h12 with h | h <;> simp [Nat.pow_mod, h]
  obtain ⟨t, ht⟩ : ∃ t, s ^ 2 = 3 * t + 1 := ⟨s ^ 2 / 3, by omega⟩
  obtain ⟨y, hydef⟩ : ∃ y : G, y = (x * n) ^ (s ^ 2) := ⟨_, rfl⟩
  have hyX : y ∈ X := by
    rw [hydef]
    exact X.pow_mem (X.mul_mem hxX (hNX hnN)) _
  have hyc : ∀ a ∈ A, a * y = y * a := fun a ha => by
    rw [hydef]
    exact ((hcommA a ha).pow_right _).eq
  have hy3r : y ^ (3 ^ r) = 1 := by
    rw [hydef, ← pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hm, mul_comm (s ^ 2)]
    exact mul_dvd_mul_left _ (dvd_pow_self s two_ne_zero)
  have hxk : x ^ (s ^ 2) = x * (x ^ 3) ^ t := by
    rw [ht, show 3 * t + 1 = 1 + 3 * t by ring, pow_add, pow_one, pow_mul]
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = (x ^ (s ^ 2))⁻¹ * y := ⟨_, rfl⟩
  have hcN : c ∈ N := by
    rw [hcdef, hydef]
    exact hpow n hnN (s ^ 2)
  have hyc' : y = x ^ (s ^ 2) * c := by
    rw [hcdef, mul_inv_cancel_left]
  have hd : (x ^ 3) ^ t * c ∈ N := N.mul_mem (N.pow_mem hx3 t) hcN
  have hyd : y = x * ((x ^ 3) ^ t * c) := by
    rw [← mul_assoc, ← hxk, ← hyc']
  have hyx : y⁻¹ * x ∈ N := by
    have e' : y⁻¹ * x = ((x ^ 3) ^ t * c)⁻¹ := by
      rw [hyd]
      group
    rw [e']
    exact N.inv_mem hd
  have hy3N : y ^ 3 ∈ N := by
    have h := N.mul_mem hx3 (hpow _ hd 3)
    rw [mul_inv_cancel_left, ← hyd] at h
    exact h
  have hy3 : y ^ 3 = 1 := by
    have hz : (y ^ 3) ^ (3 ^ r) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hy3r, one_pow]
    have hcop : Nat.Coprime (orderOf (y ^ 3)) (Nat.card N) :=
      Nat.Coprime.coprime_dvd_left (orderOf_dvd_iff_pow_eq_one.mpr hz)
        (Nat.Coprime.pow_left r ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3))
    have h1 : orderOf (y ^ 3) = 1 :=
      Nat.Coprime.eq_one_of_dvd hcop (Subgroup.orderOf_dvd_natCard N hy3N)
    exact orderOf_eq_one_iff.mp h1
  by_cases hyA : y ∈ A
  · exact ⟨y, hyA, hyX, hyx⟩
  · exfalso
    have hcomm := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hAe hyA hy3 hyc
    have hB : A ⊔ Subgroup.zpowers y = A := hAmax _ hcomm.1 le_sup_left
    have hymem : y ∈ A ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    rw [hB] at hymem
    exact hyA hymem

end CFSG.RankThree.PartTwo.Sec8.Hering611

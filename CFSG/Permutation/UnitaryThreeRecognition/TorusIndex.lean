module

public import CFSG.Permutation.UnitaryThreeRecognition.SwapIndexMain

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem nat_cube_add_one_sub (n : ℕ) (hn : 1 ≤ n) :
    n * n * n + 1 - (n + 1) = (n + 1) * n * (n - 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have : (r + 1) * (r + 1) * (r + 1) + 1 = (r + 1 + 1) * (r + 1) * r + (r + 1 + 1) := by ring
  rw [this, Nat.add_sub_cancel, Nat.add_sub_cancel]

theorem nat_mul_self_sub_one (n : ℕ) (hn : 1 ≤ n) : n * n - 1 = (n - 1) * (n + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have : (r + 1) * (r + 1) = r * (r + 1 + 1) + 1 := by ring
  rw [this, Nat.add_sub_cancel, Nat.add_sub_cancel]

theorem card_conjSwap_le_involutions [Finite G] {a b : Ω} {j : G} (hj2 : j * j = 1) :
    Nat.card (ConjSwap G j a b) ≤ Nat.card {h : G // h * h = 1 ∧ h • a = b} := by
  apply Nat.card_le_card_of_injective (fun h => (⟨h.1, by
      obtain ⟨⟨c', hc'⟩, ha'⟩ := h.2
      refine ⟨?_, ha'⟩
      rw [hc']
      calc c'⁻¹ * j * c' * (c'⁻¹ * j * c') = c'⁻¹ * (j * j) * c' := by group
        _ = 1 := by rw [hj2]; group⟩ : {h : G // h * h = 1 ∧ h • a = b}))
  intro x y hxy
  simp only [Subtype.mk.injEq] at hxy
  exact Subtype.ext hxy

theorem card_sq_eq_one_le_two {T : Subgroup G} {j : G}
    (hsq : ∀ t ∈ T, t * t = 1 → t = 1 ∨ t = j) :
    Nat.card {t : G // t ∈ T ∧ t * t = 1} ≤ 2 := by
  classical
  have : Nat.card {t : G // t ∈ T ∧ t * t = 1} ≤ Nat.card ({1, j} : Set G) := by
    apply Nat.card_le_card_of_injective (fun t => (⟨t.1, by
        rcases hsq t.1 t.2.1 t.2.2 with h | h
        · left; exact h
        · right; exact h⟩ : ({1, j} : Set G)))
    intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    exact Subtype.ext hxy
  refine this.trans ?_
  rw [Nat.card_coe_set_eq]
  calc ({1, j} : Set G).ncard ≤ ({j} : Set G).ncard + 1 := Set.ncard_insert_le 1 {j}
    _ = 2 := by rw [Set.ncard_singleton]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem index_dvd_sub_one [Finite G] {b : Ω} (hb : b ≠ a)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {s : G} (hsa : s • a = b) (hsb : s • b = a) {p f : ℕ}
    (hQcard : Nat.card Q = p ^ (3 * f))
    (hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1) :
    ∃ m : ℕ, Nat.card (pairStab G a b) = Nat.card (swapFix G a b s) * m ∧ m ∣ p ^ f - 1 := by
  have hdvd1 := hQ.card_pairStab_dvd_swapFix_mul hb hsa hsb hcomm
  rw [hQcard] at hdvd1
  have hTs_dvd : Nat.card (swapFix G a b s) ∣ Nat.card (pairStab G a b) :=
    Subgroup.card_dvd_of_le (inf_le_left : swapFix G a b s ≤ pairStab G a b)
  obtain ⟨m, hm⟩ := hTs_dvd
  have hTspos : 0 < Nat.card (swapFix G a b s) := Nat.card_pos
  have hm1 : m ∣ p ^ (3 * f) - 1 := by
    rw [hm] at hdvd1
    exact (Nat.mul_dvd_mul_iff_left hTspos).mp hdvd1
  have hm2 : m ∣ p ^ (2 * f) - 1 := by
    have : m ∣ Nat.card (pairStab G a b) := ⟨_, by rw [hm, mul_comm]⟩
    exact this.trans hTdvd
  refine ⟨m, hm, ?_⟩
  have := Nat.dvd_gcd hm1 hm2
  rw [Nat.pow_sub_one_gcd_pow_sub_one] at this
  have hg : Nat.gcd (3 * f) (2 * f) = f := by
    rw [Nat.gcd_mul_right]; norm_num
  rwa [hg] at this

theorem card_conjSwap_eq [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1) :
    Nat.card (ConjSwap G j a b) = p ^ f - 1 := by
  have hz := hQ.card_centQ_involution_eq hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hQcard
    hΩcard hTdvd
  have hc := hQ.count_identity hb htwo hcomm hj hj2 hj1 hsq
  rw [hz, hΩcard] at hc
  set q := p ^ f with hqdef
  have hq3 : p ^ (3 * f) = q * q * q := by
    rw [hqdef, ← pow_two, ← pow_succ]; ring_nf
  have hq : 3 ≤ q := le_trans hp (Nat.le_self_pow (by omega) p)
  rw [hq3] at hc
  rw [nat_cube_add_one_sub q (by omega)] at hc
  have hpos : 0 < (q + 1) * q := by positivity
  exact (Nat.eq_of_mul_eq_mul_left hpos hc).symm

theorem card_pairStab_eq_mul_swapFix [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1) :
    Nat.card (pairStab G a b) = (p ^ f - 1) * Nat.card (swapFix G a b s) := by
  classical
  have hsb : s • b = a := by rw [← hsa, ← mul_smul, hs2, one_smul]
  have hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1 := ⟨d, hTcard.symm⟩
  set q := p ^ f with hqdef
  have hq : 3 ≤ q := le_trans hp (Nat.le_self_pow (by omega) p)
  have hqodd : Odd q := hpodd.pow
  have hk := hQ.card_conjSwap_eq hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hQcard hΩcard
    hTdvd
  obtain ⟨m, hm, hmdvd⟩ := hQ.index_dvd_sub_one hb hcomm hsa hsb hQcard hTdvd
  have hTspos : 0 < Nat.card (swapFix G a b s) := Nat.card_pos
  have hinv := card_involutions_mul_le hsa hs2 hcomm (card_sq_eq_one_le_two hsq)
  have hle := card_conjSwap_le_involutions (a := a) (b := b) hj2
  have hq2m : q - 1 ≤ 2 * m := by
    have : (q - 1) * Nat.card (swapFix G a b s) ≤ (2 * m) * Nat.card (swapFix G a b s) := by
      calc (q - 1) * Nat.card (swapFix G a b s)
          ≤ Nat.card {h : G // h * h = 1 ∧ h • a = b} * Nat.card (swapFix G a b s) := by
            rw [← hk]; exact Nat.mul_le_mul_right _ hle
        _ ≤ 2 * Nat.card (pairStab G a b) := hinv
        _ = (2 * m) * Nat.card (swapFix G a b s) := by rw [hm]; ring
    exact Nat.le_of_mul_le_mul_right this hTspos
  obtain ⟨c, hc⟩ := hmdvd
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, zero_mul] at hc; omega
    · exact h
  have hc12 : c = 1 ∨ c = 2 := by
    have : m * c ≤ m * 2 := by rw [← hc]; linarith
    have hc2 : c ≤ 2 := Nat.le_of_mul_le_mul_left this hmpos
    have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; omega
    omega
  rcases hc12 with rfl | rfl
  · rw [hm, mul_comm, hc, mul_one]
  · exfalso
    have hq2 : p ^ (2 * f) - 1 = (q - 1) * (q + 1) := by
      have : p ^ (2 * f) = q * q := by rw [hqdef, ← pow_two, ← pow_mul, mul_comm]
      rw [this, nat_mul_self_sub_one q (by omega)]
    have hTs : Nat.card (swapFix G a b s) * d = 2 * (q + 1) := by
      have h1 : Nat.card (swapFix G a b s) * m * d = m * (2 * (q + 1)) := by
        rw [← hm, hTcard, hq2, hc]; ring
      have h2 : m * (Nat.card (swapFix G a b s) * d) = m * (2 * (q + 1)) := by
        rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_left hmpos h2
    obtain ⟨w, r, hrodd, hqr⟩ := Nat.exists_eq_two_pow_mul_odd (show q + 1 ≠ 0 by omega)
    have h2w : 2 ^ (w + 1) ∣ Nat.card (swapFix G a b s) := by
      have hdvd : 2 ^ (w + 1) ∣ Nat.card (swapFix G a b s) * d := by
        rw [hTs, hqr, pow_succ]
        exact ⟨r, by ring⟩
      have hcop : Nat.Coprime (2 ^ (w + 1)) d :=
        Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hd)
      exact hcop.dvd_of_dvd_mul_right hdvd
    have hfixcard : Nat.card {y : Ω // j • y = y} = q + 1 := by
      rw [hQ.card_fixedPoints hb hj, hQ.card_centQ_involution_eq hb htwo hfaith hcomm hj hj2 hj1
        hsq hpp hp hf hQcard hΩcard hTdvd]
    have heven : Even (Nat.card {y : Ω // j • y = y}) := by
      rw [hfixcard]; exact hqodd.add_one
    have hmoved : ∃ x : Ω, j • x ≠ x := by
      by_contra hall
      push Not at hall
      have : Nat.card {y : Ω // j • y = y} = Nat.card Ω :=
        Nat.card_congr (Equiv.subtypeUnivEquiv hall)
      rw [hfixcard, hΩcard] at this
      have : q + 1 < p ^ (3 * f) + 1 := by
        have : q < p ^ (3 * f) := by
          rw [hqdef]; exact Nat.pow_lt_pow_right (by omega) (by omega)
        omega
      omega
    have := two_pow_dvd_card_fixed hb htwo hcomm hj hj2 hj1 hsq heven hmoved hsa hsb h2w
    rw [hfixcard, hqr, pow_succ] at this
    have : 2 ∣ r := by
      obtain ⟨k, hk⟩ := this
      have hpos : 0 < 2 ^ w := by positivity
      have : 2 ^ w * r = 2 ^ w * (2 * k) := by rw [hk]; ring
      exact ⟨k, Nat.eq_of_mul_eq_mul_left hpos this⟩
    exact (Nat.not_even_iff_odd.mpr hrodd) (even_iff_two_dvd.mpr this)

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition

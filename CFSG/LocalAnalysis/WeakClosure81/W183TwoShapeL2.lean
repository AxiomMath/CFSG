module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoShapeCard
import CFSG.LocalAnalysis.SeitzReduction.CrossChar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf
  (LieOrderFormulasInput lieOrderNumerator lieOrderDivisor)

private theorem w183b5_mono (s a : ℕ) (h : s ≤ a) :
    (s + 1) * (s * (s + 2)) ≤ (a + 1) * (a * (a + 2)) :=
  Nat.mul_le_mul (by omega) (Nat.mul_le_mul h (by omega))

private theorem w183b5_l2_arith {q M : ℕ} (hq : 11 ≤ q)
    (hM : q * ((q - 1) * (q + 1)) = 2 * M) (hc : Tail1812Orders M) : q = 25 := by
  obtain ⟨s, rfl⟩ : ∃ s, q = s + 1 := ⟨q - 1, by omega⟩
  have hs : 10 ≤ s := by omega
  have h' : (s + 1) * (s * (s + 2)) = 2 * M := by
    simpa only [show s + 1 - 1 = s by omega, show s + 1 + 1 = s + 2 by omega] using hM
  simp only [Tail1812Orders] at hc
  rcases hc with hc | hc | hc | hc | hc | hc | hc
  · rw [hc] at h'
    have := w183b5_mono 10 s hs
    norm_num at this
    omega
  · rw [hc] at h'
    rcases le_or_gt s 48 with hle | hgt
    · have := w183b5_mono s 48 hle
      norm_num at this
      omega
    · have hge : 49 ≤ s := by omega
      have := w183b5_mono 49 s hge
      norm_num at this
      omega
  · rw [hc] at h'
    have := w183b5_mono 10 s hs
    norm_num at this
    omega
  · rw [hc] at h'
    rcases le_or_gt s 124 with hle | hgt
    · have := w183b5_mono s 124 hle
      norm_num at this
      omega
    · have hge : 125 ≤ s := by omega
      have := w183b5_mono 125 s hge
      norm_num at this
      omega
  · rw [hc] at h'
    rcases le_or_gt s 24 with hle | hgt
    · by_contra hne
      have hs23 : s ≤ 23 := by omega
      have := w183b5_mono s 23 hs23
      norm_num at this
      omega
    · have hge : 25 ≤ s := by omega
      have := w183b5_mono 25 s hge
      norm_num at this
      omega
  · rw [hc] at h'
    rcases le_or_gt s 209 with hle | hgt
    · have := w183b5_mono s 209 hle
      norm_num at this
      omega
    · have hge : 210 ≤ s := by omega
      have := w183b5_mono 210 s hge
      norm_num at this
      omega
  · rw [hc] at h'
    rcases le_or_gt s 36 with hle | hgt
    · have := w183b5_mono s 36 hle
      norm_num at this
      omega
    · have hge : 37 ≤ s := by omega
      have := w183b5_mono 37 s hge
      norm_num at this
      omega

private theorem w183b5_psp_order {p M : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : M * lieOrderDivisor .PSp 2 (p ^ 1) = lieOrderNumerator .PSp 2 (p ^ 1)) :
    M * 2 = p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) := by
  have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
    rw [pow_one]
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    rw [hk, show 2 * k + 1 - 1 = 2 * k by omega]
    exact Nat.gcd_eq_left (Dvd.intro k rfl)
  have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have hc' : M * Nat.gcd 2 (p ^ 1 - 1) =
      (p ^ 1) ^ (2 ^ 2) * ∏ i ∈ Finset.Icc 1 2, ((p ^ 1) ^ (2 * i) - 1) := hM
  rw [hg, hI, Finset.prod_pair (by norm_num)] at hc'
  simpa using hc'

private theorem w183b5_psp_arith {p M : ℕ} (hp7 : 7 ≤ p)
    (hM : M * 2 = p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1))) : 4680000 < M := by
  have h1 : 7 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left hp7 4
  have h2 : 7 ^ 2 - 1 ≤ p ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hp7 2) 1
  have h3 : 7 ^ 4 - 1 ≤ p ^ 4 - 1 := Nat.sub_le_sub_right h1 1
  have hbig : 7 ^ 4 * ((7 ^ 2 - 1) * (7 ^ 4 - 1)) ≤ p ^ 4 * ((p ^ 2 - 1) * (p ^ 4 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  rw [← hM] at hbig
  norm_num at hbig
  omega

theorem eq_of_isL2_card_mem (hO : LieOrderFormulasInput) {X : Type} [Group X] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : 9 < p ^ e) (h : CFSG.Quasithin.F6.IsL2 p e X)
    (hc : Tail1812Orders (Nat.card X)) : p ^ e = 25 := by
  have hmodel : LieModel X .PSL 2 p e := Or.inl ⟨by decide, h⟩
  have hM := (hO X .PSL 2 p e hmodel.admissible hmodel).2.1
  have hqodd : Odd (p ^ e) := (hp.odd_of_ne_two hp2).pow
  have h2M : p ^ e * ((p ^ e - 1) * (p ^ e + 1)) = 2 * Nat.card X :=
    (CFSG.SeitzReduction.CrossChar.two_mul_card_eq_of_PSL_two_odd (q' := p ^ e)
      (by omega) hqodd hM).symm
  have hq11 : 11 ≤ p ^ e := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  exact w183b5_l2_arith hq11 h2M hc

theorem eq_of_psp_card_mem (hO : LieOrderFormulasInput) {X : Type} [Group X] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : LieModel X .PSp 2 p 1)
    (hc : Tail1812Orders (Nat.card X)) : p = 3 ∨ p = 5 := by
  have hM := w183b5_psp_order hp hp2 (hO X .PSp 2 p 1 h.admissible h).2.1
  have hcard_le : Nat.card X ≤ 4680000 := by
    simp only [Tail1812Orders] at hc
    rcases hc with hc | hc | hc | hc | hc | hc | hc <;> omega
  by_contra hcon
  have hp3 : p ≠ 3 := fun h3 => hcon (Or.inl h3)
  have hp5 : p ≠ 5 := fun h5 => hcon (Or.inr h5)
  have hp7 : 7 ≤ p := by
    rcases hp.eq_two_or_odd' with h2 | hodd
    · exact absurd h2 hp2
    · obtain ⟨k, rfl⟩ := hodd
      have hk1 : 1 ≤ k := by have := hp.two_le; omega
      omega
  have := w183b5_psp_arith hp7 hM
  omega

end CFSG.LocalAnalysis.WeakClosure81

end

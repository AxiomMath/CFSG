module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.FieldDegree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

private theorem w135c2_psu_selfdual_bounds {n : ℕ} (hn : 3 ≤ n) {S : Finset (Fin n)}
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hne : S ≠ ∅) (hsd : S.image labelStar = S) :
    6 ≤ orbitSize S ∧ 4 ≤ movedOrbit (by omega : 2 ≤ n) S := by
  classical
  have hn2 : 2 ≤ n := by omega
  by_cases h2 : 2 ≤ S.card
  · have hM := two_mul_two_mul_sub_three_le_movedOrbit hn2 h0 (by omega : 3 ≤ S.card + 1)
    have hsplit := movedOrbit_add_fixedOrbit hn2 S
    have hM6 : 6 ≤ movedOrbit (by omega : 2 ≤ n) S := by omega
    have hMN : movedOrbit (by omega : 2 ≤ n) S ≤ orbitSize S := by omega
    exact ⟨le_trans hM6 hMN, le_trans (by norm_num : 4 ≤ 6) hM6⟩
  · have hcard1 : S.card = 1 := by
      have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      omega
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard1
    have hmem : labelStar j ∈ ({j} : Finset (Fin n)) := by
      rw [← hsd]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_singleton_self j, rfl⟩
    have hfix : labelStar j = j := Finset.mem_singleton.mp hmem
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h
      apply h0
      rw [Finset.mem_singleton]
      exact Fin.ext h.symm
    have h2j : 2 * (j : ℕ) = n := by
      have h1 := congrArg Fin.val hfix
      rw [labelStar_eq_of_ne_zero hj0] at h1
      simp only [Fin.val_mk] at h1
      have := j.isLt
      omega
    have hj2 : 2 ≤ (j : ℕ) := by omega
    have hn4 : 4 ≤ n := by omega
    refine ⟨?_, ?_⟩
    · rw [orbitSize_singleton]
      have hjc := choose_two_le_choose (n := n) (k := (j : ℕ)) hj2 (by omega)
      have hc := two_mul_choose_two n
      have h12 : 12 ≤ n * (n - 1) := by
        calc 12 = 4 * 3 := by norm_num
          _ ≤ n * (n - 1) := Nat.mul_le_mul hn4 (by omega : 3 ≤ n - 1)
      omega
    · rw [movedOrbit_singleton hn2 (j := j) (by omega : 1 ≤ (j : ℕ))]
      have hle := le_choose (n := n - 2) (k := (j : ℕ) - 1) (by omega) (by omega)
      have htwo : 2 ≤ n - 2 := by omega
      omega

theorem w135c2_psu_outer_multi {n f s u : ℕ} (hn : 3 ≤ n) (hs : 1 ≤ s) (hu : 1 ≤ u)
    (hsu : s * u ≤ 3) (ε : Fin f → Finset (Fin n))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r) (r₁ r₂ : Fin f) (hr : r₁ ≠ r₂)
    (h₁ : ε r₁ ≠ ∅) (h₂ : ε r₂ ≠ ∅)
    (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hns : (univ.filter fun r => ε r ≠ ∅).card ≤ 2 →
      (∃ r, (ε r).image labelStar ≠ ε r) → 2 * f ≤ s)
    (hmv : movedTop (by omega : 2 ≤ n) ε ≤ 4 * u) : False := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hu3 : u ≤ 3 := by
    have h1 : u ≤ s * u := by
      calc u = 1 * u := (one_mul u).symm
        _ ≤ s * u := Nat.mul_le_mul_right u hs
    omega
  have hmv12 : movedTop (by omega : 2 ≤ n) ε ≤ 12 := by omega
  set T : Finset (Fin f) := univ.filter (fun r => ε r ≠ ∅) with hT
  have hr1T : r₁ ∈ T := by
    rw [hT]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ r₁, h₁⟩
  have hr2T : r₂ ∈ T := by
    rw [hT]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ r₂, h₂⟩
  have hsubT : ({r₁, r₂} : Finset (Fin f)) ⊆ T := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hr1T
    · exact hr2T
  have h2T : 2 ≤ T.card := by
    have hc := Finset.card_le_card hsubT
    rwa [Finset.card_pair hr] at hc
  have hTle2 : T.card ≤ 2 := by
    by_contra hle
    have h3T : 3 ≤ T.card := by omega
    have hthree := two_mul_pow_le_movedTop_of_three hn2 ε h0 (by rwa [← hT])
    have hpow : 9 ≤ n ^ (T.card - 1) := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
        _ ≤ n ^ (T.card - 1) :=
            Nat.pow_le_pow_right (by omega : 0 < n) (by omega : 2 ≤ T.card - 1)
    have h18 : 18 ≤ movedTop (by omega : 2 ≤ n) ε := by
      calc 18 = 2 * 9 := by norm_num
        _ ≤ 2 * n ^ (T.card - 1) := Nat.mul_le_mul_left 2 hpow
        _ ≤ movedTop (by omega : 2 ≤ n) ε := hthree
    omega
  have hTcard : T.card = 2 := by omega
  have hTpair : T = {r₁, r₂} := by
    have hle : T.card ≤ ({r₁, r₂} : Finset (Fin f)).card := by
      rw [Finset.card_pair hr]
      exact hTcard.le
    exact (Finset.eq_of_subset_of_card_le hsubT hle).symm
  have hother : ∀ i, i ≠ r₁ → i ≠ r₂ → ε i = ∅ := by
    intro i hi1 hi2
    by_contra hne
    have hiT : i ∈ T := by
      rw [hT]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
    rw [hTpair, Finset.mem_insert, Finset.mem_singleton] at hiT
    rcases hiT with h | h
    · exact hi1 h
    · exact hi2 h
  by_cases hsd : ∃ r, (ε r).image labelStar ≠ ε r
  · have h2f : 2 * f ≤ s := hns hTle2 hsd
    have hf2 : 2 ≤ f := by
      have hc := Finset.card_le_card (Finset.subset_univ ({r₁, r₂} : Finset (Fin f)))
      rw [Finset.card_pair hr, Finset.card_univ, Fintype.card_fin] at hc
      exact hc
    have hs4 : 4 ≤ s := by omega
    have : 4 ≤ s * u := by
      calc 4 = 4 * 1 := by norm_num
        _ ≤ s * u := Nat.mul_le_mul hs4 hu
    omega
  · have hall : ∀ r, (ε r).image labelStar = ε r := by
      intro r
      by_contra h
      exact hsd ⟨r, h⟩
    have hbd1 := w135c2_psu_selfdual_bounds hn (h0 r₁) h₁ (hall r₁)
    have hbd2 := w135c2_psu_selfdual_bounds hn (h0 r₂) h₂ (hall r₂)
    have hformula := movedTop_of_two hn2 ε hr hother
    have hM1 : 4 ≤ movedOrbit (by omega : 2 ≤ n) (ε r₁) := hbd1.2
    have hN2 : 6 ≤ orbitSize (ε r₂) := hbd2.1
    have h24 : 24 ≤ movedTop (by omega : 2 ≤ n) ε := by
      rw [hformula]
      calc 24 = 4 * 6 := by norm_num
        _ ≤ movedOrbit (by omega : 2 ≤ n) (ε r₁) * orbitSize (ε r₂) :=
            Nat.mul_le_mul hM1 hN2
        _ ≤ movedOrbit (by omega : 2 ≤ n) (ε r₁) * orbitSize (ε r₂) +
            movedOrbit (by omega : 2 ≤ n) (ε r₂) *
              (orbitSize (ε r₁) - movedOrbit (by omega : 2 ≤ n) (ε r₁)) :=
            Nat.le_add_right _ _
    omega

end CFSG.LocalAnalysis.WeakClosure81

module

public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthCent
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements

public section

open CFSG.SignalizerFunctorTheorem.CatalogBridge CFSG.SignalizerFunctorTheorem.NonLocal.Orth
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal (ringChar_eq_of_card_eq)

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem le_pow_sub_four (q : ℕ) (hq : 2 ≤ q) (d : ℕ) (hd : 8 ≤ d) : d ≤ q ^ (d - 4) := by
  induction d, hd using Nat.le_induction with
  | base =>
    calc 8 ≤ 2 ^ 4 := by norm_num
      _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  | succ d hd ih =>
    have h1 : d + 1 - 4 = (d - 4) + 1 := by omega
    rw [h1, pow_succ]
    have := Nat.mul_le_mul ih hq
    omega

theorem orth_dq (q d : ℕ) (hq : 2 ≤ q) (hd : 8 ≤ d ∨ (d = 7 ∧ 3 ≤ q)) : d ≤ q ^ (d - 4) := by
  rcases hd with hd | ⟨rfl, hq3⟩
  · exact le_pow_sub_four q hq d hd
  · have h1 : 3 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
    show 7 ≤ q ^ 3
    omega

theorem subfieldNonLocalizedOrthogonal : SubfieldNonLocalizedOrthogonal := by
  refine ⟨?_, ?_, ?_⟩
  · intro n ℓ e p hadm hp hp3 hpℓ K _ _ k hk hK σ hσ hσk
    obtain ⟨hℓ, he, hn3, hℓ2⟩ := hadm
    have hp2 : p ≠ 2 := by omega
    have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
    have h2K : ringChar K ≠ 2 := by
      rw [ringChar_eq_of_card_eq hℓ hf hK]
      exact hℓ2
    have S := subfieldSetup_odd k hσk hp hp2 hσ hn3 (Ring.two_ne_zero h2K)
    have hq3 : 3 ≤ Nat.card k := by
      have h1 : ℓ ≤ ℓ ^ e := Nat.le_self_pow (by omega) ℓ
      have h2 := hℓ.two_le
      rw [hk]
      omega
    refine nonLocalized_orthogonalSubfield k S.hext S.hnd₀ S.hnd S.hT₀ (by omega)
      (orth_dq _ _ (by omega) ?_)
    rcases Nat.lt_or_ge n 4 with h | h
    · right
      exact ⟨by omega, hq3⟩
    · left
      omega
  · intro n ℓ e p hadm hp hp3 hpℓ K _ _ k hk hK σ hσ hσk
    obtain ⟨hℓ, he, hn4⟩ := hadm
    have hp2 : p ≠ 2 := by omega
    have S := subfieldSetup_plus k hσk hp hp2 hσ (by omega : 3 ≤ n)
    have hq2 : 2 ≤ Nat.card k := by
      have h1 : ℓ ≤ ℓ ^ e := Nat.le_self_pow (by omega) ℓ
      have h2 := hℓ.two_le
      rw [hk]
      omega
    exact nonLocalized_orthogonalSubfield k S.hext S.hnd₀ S.hnd S.hT₀ (by omega)
      (orth_dq _ _ hq2 (Or.inl (by omega)))
  · intro n ℓ e p hadm hp hp3 hpℓ hn K _ _ k hk hK σ hσ hσk b c' hirr
    obtain ⟨hℓ, he, hn4⟩ := hadm
    have hp2 : p ≠ 2 := by omega
    have hdeg := finrank_subfield_eq k hℓ he hk hK
    have S := subfieldSetup_minus k hσk hp hp2 hσ hn4 hdeg b c' hirr
    have hq2 : 2 ≤ Nat.card k := by
      have h1 : ℓ ≤ ℓ ^ e := Nat.le_self_pow (by omega) ℓ
      have h2 := hℓ.two_le
      rw [hk]
      omega
    exact nonLocalized_orthogonalSubfield k S.hext S.hnd₀ S.hnd S.hT₀ (by omega)
      (orth_dq _ _ hq2 (Or.inl (by omega)))

end CFSG.SignalizerFunctorTheorem.NonLocal

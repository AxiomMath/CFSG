module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3CardSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3CardTab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3OutThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3OutTab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16t3_small_shape_of_sum (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hsum : SumOfNatShape (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3)
    (h3 : 3 ∉ D.sig) :
    ∃ n : ℕ,
      (IsSLn ↥(lBar V₀ V hV L) n 1 ∧ n < 8) ∨
      (IsSpn ↥(lBar V₀ V hV L) n 1 ∧ n < 8) ∨
      (IsOmegaPlus ↥(lBar V₀ V hV L) n 1 ∧ n < 8) ∨
      (IsOmegaMinus ↥(lBar V₀ V hV L) n 1 ∧ n < 10) ∨
      (UC22.IsAlt ↥(lBar V₀ V hV L) n ∧ n < 12) := by
  obtain ⟨n, hsl | hsp | hop | hom | halt⟩ := hsum
  · refine ⟨n, Or.inl ⟨hsl.1, ?_⟩⟩
    by_contra hn
    exact h3 (h.three_mem_sig_of_shape hGA hSchur ⟨n, Or.inl ⟨hsl.1, not_lt.1 hn⟩⟩)
  · refine ⟨n, Or.inr (Or.inl ⟨hsp.1, ?_⟩)⟩
    by_contra hn
    exact h3 (h.three_mem_sig_of_shape hGA hSchur ⟨n, Or.inr (Or.inl ⟨hsp.1, not_lt.1 hn⟩)⟩)
  · refine ⟨n, Or.inr (Or.inr (Or.inl ⟨hop.1, ?_⟩))⟩
    by_contra hn
    exact h3 (h.three_mem_sig_of_shape hGA hSchur
      ⟨n, Or.inr (Or.inr (Or.inl ⟨hop.1, not_lt.1 hn⟩))⟩)
  · refine ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hom.1, ?_⟩)))⟩
    by_contra hn
    exact h3 (h.three_mem_sig_of_shape hGA hSchur
      ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hom.1, not_lt.1 hn⟩)))⟩)
  · refine ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ⟨halt.1, ?_⟩)))⟩
    by_contra hn
    exact h3 (h.three_mem_sig_of_shape hGA hSchur
      ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ⟨halt.1, not_lt.1 hn⟩)))⟩)

theorem S16gRowCtx.false_of_not_three_mem_sig (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hsum : SumOfNatShape (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 3)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h3 : 3 ∉ D.sig)
    (h7 : 7 ∉ D.sig ∨ ¬ (IsSLn ↥(lBar V₀ V hV L) 6 1 ∨ IsSLn ↥(lBar V₀ V hV L) 7 1)) :
    False := by
  classical
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  haveI : Finite ↥(lBar V₀ V hV L) := Subtype.finite
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hp3 : p ≠ 3 := fun hpe => h3 (hpe ▸ hpσ)
  have hp4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  have hp2le : 2 ≤ p := hp.two_le
  have hp5 : 5 ≤ p := by omega
  have hrk : 3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) := h.three_le_pRank hpσ
  have hrk' : 3 ≤ CFSG.pRank p (Mbar D.M V₀ V hV) := by
    rw [UC6.groupPRank_eq_pRank]
    exact hrk
  have hshape := s16t3_small_shape_of_sum h hGA hSchur hsum h3
  have hvals := s16t3_small_shape_valuations h.quasi hshape
  have hnot3 := s16t3_not_three_dvd_outer h.quasi hshape
  rcases hT.card_irrSet_eq with hIrr | hIrr
  · exact hnot3 (hT.three_dvd_card_outer hIrr)
  · have hdvd7 : Nat.card ↥(Mbar D.M V₀ V hV) ∣
        336 * Nat.card ↥(lBar V₀ V hV L) := hT.card_dvd_of_seven hIrr
    obtain ⟨E, hEM, _hEea, hEcard⟩ :=
      c23_exists_elemAbelian_card_pow (p := p) (M := Mbar D.M V₀ V hV) (k := 3) hp hrk'
    have hpdvdM : p ^ 3 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
      rw [← hEcard]
      exact Subgroup.card_dvd_of_le hEM
    have hpdvd : p ^ 3 ∣ 336 * Nat.card ↥(lBar V₀ V hV L) := hpdvdM.trans hdvd7
    by_cases hpe7 : p = 7
    · have hpdvd7 : 7 ^ 3 ∣ 336 * Nat.card ↥(lBar V₀ V hV L) := by
        simpa [hpe7] using hpdvd
      have h72 : 7 ^ 2 ∣ Nat.card ↥(lBar V₀ V hV L) := by
        have h := hpdvd7
        have h73 : (7 : ℕ) ^ 3 = 7 * 7 ^ 2 := by norm_num
        have h336 : (336 : ℕ) = 7 * 48 := by norm_num
        rw [h73, h336, mul_assoc] at h
        have hc : 7 ^ 2 ∣ 48 * Nat.card ↥(lBar V₀ V hV L) :=
          (Nat.mul_dvd_mul_iff_left (a := 7) (b := 7 ^ 2)
            (c := 48 * Nat.card ↥(lBar V₀ V hV L))
            (show 0 < (7 : ℕ) by norm_num)).1 h
        exact (show Nat.Coprime (7 ^ 2) 48 by
          rw [Nat.coprime_pow_left_iff (show 0 < 2 by norm_num) 7 48]
          norm_num).dvd_of_dvd_mul_left hc
      have hpσ7 : 7 ∈ D.sig := by simpa [hpe7] using hpσ
      exact h7.elim (fun h7n => h7n hpσ7) (fun h7n => h7n (hvals.2 h72))
    · have hnotdvd : ¬ p ∣ 336 := by
        intro hpd
        rw [show (336 : ℕ) = 2 ^ 4 * 3 * 7 by norm_num] at hpd
        rcases hp.dvd_mul.mp hpd with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
          · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
        · exact hpe7 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1 h)
      have hcop : Nat.Coprime (p ^ 3) 336 :=
        (Nat.coprime_pow_left_iff (show 0 < 3 by norm_num) p 336).2
          ((hp.coprime_iff_not_dvd).2 hnotdvd)
      exact hvals.1 p hp hp5 (hcop.dvd_of_dvd_mul_left hpdvd)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

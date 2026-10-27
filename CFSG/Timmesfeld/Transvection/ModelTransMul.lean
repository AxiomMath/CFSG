module

public import CFSG.Timmesfeld.Transvection.ModelRankSp

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM

namespace ModelRank

theorem pow_two_pow_mulVec_ne_self {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [Field F] [CharP F 2] {M : Matrix ι ι F} {p : ι → F} (hp : p ≠ 0) {τ : F} (hτ : τ ≠ 0)
    (h : (M ^ 2 + 1) *ᵥ p = τ • (M *ᵥ p)) (k : ℕ) : M ^ (2 ^ k) *ᵥ p ≠ p := by
  intro hk
  have hcomm : Commute (M ^ 2 + 1) M :=
    ((Commute.refl M).pow_left 2).add_left (Commute.one_left M)
  have hj : ∀ j : ℕ, (M ^ 2 + 1) ^ j *ᵥ p = τ ^ j • (M ^ j *ᵥ p) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ (M ^ 2 + 1) j, ← mulVec_mulVec, h, mulVec_smul, mulVec_mulVec,
        (hcomm.pow_left j).eq, ← mulVec_mulVec, ih, mulVec_smul, smul_smul, mulVec_mulVec,
        ← pow_succ' M j, ← pow_succ' τ j]
  have h2k : M ^ (2 ^ (k + 1)) *ᵥ p = p := by
    rw [pow_succ (2 : ℕ) k, pow_mul, sq, ← mulVec_mulVec, hk, hk]
  have : Nonempty ι := by
    obtain ⟨i, -⟩ := Function.ne_iff.1 hp
    exact ⟨i⟩
  have hfrob : (M ^ 2 + 1) ^ (2 ^ k) = M ^ (2 ^ (k + 1)) + 1 := by
    rw [add_pow_char_pow_of_commute 2 k (Commute.one_right (M ^ 2)), one_pow, ← pow_mul,
      ← pow_succ']
  have h0 : τ ^ (2 ^ k) • p = 0 := by
    rw [← hk, ← hj, hfrob, add_mulVec, one_mulVec, h2k, ← two_smul F p, CharTwo.two_eq_zero,
      zero_smul]
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact pow_ne_zero _ hτ h1
  · exact hp h1

theorem ne_one_pow_two_pow_of_spTrans_mul {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {p q : Fin n ⊕ Fin n → F} (hpq : spForm p q ≠ 0) {c c' : F} (hc : c ≠ 0) (hc' : c' ≠ 0)
    {g : StatedSp n F} (hg : SpExtras.mat n F g = spTrans p c * spTrans q c') (k : ℕ) :
    g ^ (2 ^ k) ≠ 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hqp : spForm q p = spForm p q := by rw [spForm_comm p q, CharTwo.neg_eq]
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hpq (by simp [spForm])
  have hMp : SpExtras.mat n F g *ᵥ p =
      (1 + c * c' * spForm p q ^ 2) • p + (c' * spForm p q) • q := by
    rw [hg, ← mulVec_mulVec, spTrans_mulVec, spTrans_mulVec, hqp, spForm_add_right,
      spForm_self, spForm_smul_right']
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hMq : SpExtras.mat n F g *ᵥ q = (c * spForm p q) • p + q := by
    rw [hg, ← mulVec_mulVec, spTrans_mulVec, spTrans_mulVec, spForm_self, mul_zero, zero_smul,
      add_zero, add_comm]
  have hQ : (SpExtras.mat n F g ^ 2 + 1) *ᵥ p =
      (c * c' * spForm p q ^ 2) • (SpExtras.mat n F g *ᵥ p) := by
    rw [add_mulVec, one_mulVec, sq (SpExtras.mat n F g), ← mulVec_mulVec, hMp, mulVec_add,
      mulVec_smul, mulVec_smul, hMp, hMq]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination ((1 + c * c' * spForm p q ^ 2) * p i + c' * spForm p q * q i) * h2
  have hτ : c * c' * spForm p q ^ 2 ≠ 0 := mul_ne_zero (mul_ne_zero hc hc') (pow_ne_zero 2 hpq)
  intro h1
  exact pow_two_pow_mulVec_ne_self hp0 hτ hQ k (by rw [← map_pow, h1, map_one, one_mulVec])

end ModelRank

end CFSG.Timmesfeld.Transvection

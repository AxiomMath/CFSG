module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_11

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (13) -/

public theorem claim_13_beta_sum_linear
    {E : Type*} [Field E] [CharP E 2] {alpha beta : E}
    (hbeta : beta ≠ 0)
    (halpha : alpha = beta + beta⁻¹)
    (i : ℕ) (hi : 1 ≤ i) :
    alpha * (beta ^ i + (beta⁻¹) ^ i) +
        (beta ^ (i - 1) + (beta⁻¹) ^ (i - 1)) =
      beta ^ (i + 1) + (beta⁻¹) ^ (i + 1) := by
  subst alpha
  cases i with
  | zero => omega
  | succ j =>
      have hmul_left :
          beta * beta ^ (j + 1) = beta ^ (j + 2) := by
        simpa [Nat.add_assoc] using (pow_succ' beta (j + 1)).symm
      have hmul_right :
          beta⁻¹ * (beta⁻¹) ^ (j + 1) = (beta⁻¹) ^ (j + 2) := by
        simpa [Nat.add_assoc] using (pow_succ' beta⁻¹ (j + 1)).symm
      have hcross_left : beta⁻¹ * beta ^ (j + 1) = beta ^ j := by
        rw [pow_succ]
        calc
          beta⁻¹ * (beta ^ j * beta) =
              beta ^ j * (beta⁻¹ * beta) := by ring
          _ = beta ^ j := by
            rw [inv_mul_cancel₀ hbeta, mul_one]
      have hcross_right : beta * (beta⁻¹) ^ (j + 1) = (beta⁻¹) ^ j := by
        rw [pow_succ]
        calc
          beta * ((beta⁻¹) ^ j * beta⁻¹) =
              (beta⁻¹) ^ j * (beta * beta⁻¹) := by ring
          _ = (beta⁻¹) ^ j := by
            rw [mul_inv_cancel₀ hbeta, mul_one]
      calc
        (beta + beta⁻¹) * (beta ^ (j + 1) + (beta⁻¹) ^ (j + 1)) +
            (beta ^ ((j + 1) - 1) + (beta⁻¹) ^ ((j + 1) - 1)) =
            (beta * beta ^ (j + 1) + beta * (beta⁻¹) ^ (j + 1)) +
              (beta⁻¹ * beta ^ (j + 1) +
                beta⁻¹ * (beta⁻¹) ^ (j + 1)) +
              (beta ^ j + (beta⁻¹) ^ j) := by
          simp
          ring
        _ = beta ^ (j + 2) + (beta⁻¹) ^ (j + 2) := by
          rw [hmul_left, hmul_right, hcross_left, hcross_right]
          ring_nf
          simp [CharTwo.two_eq_zero]

public theorem claim_13_beta_sum_step
    {E : Type*} [Field E] [CharP E 2] {alpha beta : E}
    (hbeta : beta ≠ 0)
    (halpha : alpha = beta + beta⁻¹)
    (i : ℕ) (hi : 1 ≤ i)
    (hden_i : beta ^ i + (beta⁻¹) ^ i ≠ 0)
    (_hden_succ : beta ^ (i + 1) + (beta⁻¹) ^ (i + 1) ≠ 0) :
    (alpha + (beta ^ (i - 1) + (beta⁻¹) ^ (i - 1)) /
        (beta ^ i + (beta⁻¹) ^ i))⁻¹ =
      (beta ^ i + (beta⁻¹) ^ i) /
        (beta ^ (i + 1) + (beta⁻¹) ^ (i + 1)) := by
  have hsum :
      alpha + (beta ^ (i - 1) + (beta⁻¹) ^ (i - 1)) /
          (beta ^ i + (beta⁻¹) ^ i) =
          (beta ^ (i + 1) + (beta⁻¹) ^ (i + 1)) /
          (beta ^ i + (beta⁻¹) ^ i) := by
    let B := beta ^ i + (beta⁻¹) ^ i
    let A := beta ^ (i - 1) + (beta⁻¹) ^ (i - 1)
    let C := beta ^ (i + 1) + (beta⁻¹) ^ (i + 1)
    have hlin : alpha * B + A = C := by
      dsimp [A, B, C]
      exact claim_13_beta_sum_linear hbeta halpha i hi
    have hB : B ≠ 0 := by
      simpa [B] using hden_i
    rw [eq_div_iff_mul_eq hB]
    calc
      (alpha + A / B) * B = alpha * B + A := by
        field_simp [hB]
      _ = C := hlin
  rw [hsum]
  field_simp [hden_i, _hden_succ]

public theorem claim_13
    (E : Type*) [Field E] [CharP E 2] (m : ℕ) (alpha beta : E)
    (u : ℕ → E) (hcoord_beta_ne_zero : beta ≠ 0)
    (hcoord_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hcoord_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hcoord_initial : u 1 = 0)
    (hcoord_denominator_nonzero : ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
      beta ^ i + (beta⁻¹) ^ i ≠ 0) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
      u i = (beta ^ (i - 1) + (beta⁻¹) ^ (i - 1)) /
      (beta ^ i + (beta⁻¹) ^ i) := by
  have halpha : alpha = beta + beta⁻¹ :=
    alpha_eq_beta_add_inv_of_characteristic_root
      hcoord_beta_ne_zero hcoord_beta_characteristic_root
  have hden := hcoord_denominator_nonzero
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi hle
      cases i with
      | zero => omega
      | succ j =>
          cases j with
          | zero =>
              have hnum : beta ^ 0 + (beta⁻¹) ^ 0 = (0 : E) := by
                simp [CharTwo.add_self_eq_zero]
              rw [hcoord_initial, hnum]
              simp
          | succ j =>
              let k : ℕ := Nat.succ j
              have hk_lt_i : k < Nat.succ (Nat.succ j) := by
                simp [k]
              have hk_one : 1 ≤ k := by
                simp [k]
              have hk_le : k ≤ m - 1 := by
                omega
              have hk_lt : k < m - 1 := by
                omega
              have hsucc_one : 1 ≤ k + 1 := by
                omega
              have hsucc_le : k + 1 ≤ m - 1 := by
                omega
              have hprev :=
                ih k hk_lt_i hk_one hk_le
              have hden_k := hden k hk_one hk_le
              have hden_succ := hden (k + 1) hsucc_one hsucc_le
              have hstep :=
                claim_13_beta_sum_step hcoord_beta_ne_zero halpha k hk_one
                  hden_k hden_succ
              have hsum_ne :
                  alpha +
                      (beta ^ (k - 1) + (beta⁻¹) ^ (k - 1)) /
                        (beta ^ k + (beta⁻¹) ^ k) ≠ 0 := by
                intro hzero
                have hquot_zero :
                    (beta ^ k + (beta⁻¹) ^ k) /
                        (beta ^ (k + 1) + (beta⁻¹) ^ (k + 1)) = 0 := by
                  rw [← hstep]
                  simpa [inv_pow] using hzero
                exact (div_ne_zero hden_k hden_succ) hquot_zero
              have hnostop : u k ≠ alpha := by
                intro huk
                apply hsum_ne
                rw [← hprev, huk]
                exact CharTwo.add_self_eq_zero alpha
              have hrec := hcoord_recurrence_u k hnostop
              rw [hrec, hprev]
              simpa [inv_pow] using hstep

end PFchapter4section2
end CFSG.BenderSuzuki

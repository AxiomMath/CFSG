module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_13

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (14) -/

public structure Section2SequenceClosedData
    (E : Type*) [Field E] (m : ℕ) (zeta alpha beta : E)
    (tau : E → E) (u d : ℕ → E) : Prop where
  u_closed : ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
    u i = (beta ^ (i - 1) + (beta⁻¹) ^ (i - 1)) /
      (beta ^ i + (beta⁻¹) ^ i)
  d_closed : ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
    d i = zeta ^ i * tau (((beta ^ i + (beta⁻¹) ^ i) / alpha) ^ 2)
  denominator_nonzero : ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
    beta ^ i + (beta⁻¹) ^ i ≠ 0

public theorem claim_14
    (E : Type*) [Field E] [CharP E 2] (m : ℕ) (zeta alpha beta : E)
    (tau : E → E) (u d : ℕ → E) (hcoord_beta_ne_zero : beta ≠ 0)
    (hcoord_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hcoord_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hcoord_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hcoord_initial : u 1 = 0 ∧ d 1 = zeta)
    (hcoord_alpha_ne_zero : alpha ≠ 0)
    (hcoord_tau_one : tau 1 = 1)
    (hcoord_tau_mul : ∀ x y : E, tau (x * y) = tau x * tau y)
    (hcoord_denominator_nonzero : ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
      beta ^ i + (beta⁻¹) ^ i ≠ 0) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
      d i = zeta ^ i * tau (((beta ^ i + (beta⁻¹) ^ i) / alpha) ^ 2) := by
  have halpha : alpha = beta + beta⁻¹ :=
    alpha_eq_beta_add_inv_of_characteristic_root
      hcoord_beta_ne_zero hcoord_beta_characteristic_root
  have hden := hcoord_denominator_nonzero
  have htau_base : tau (((beta + beta⁻¹) / alpha) ^ 2) = 1 := by
    rw [← halpha]
    simp [hcoord_alpha_ne_zero, hcoord_tau_one]
  have htau_step : ∀ i : ℕ, 1 ≤ i → i < m - 1 →
      tau (((beta ^ i + (beta⁻¹) ^ i) / alpha) ^ 2) *
          tau (((u (i + 1))⁻¹) ^ 2) =
        tau (((beta ^ (i + 1) + (beta⁻¹) ^ (i + 1)) / alpha) ^ 2) := by
    intro i hi hlt
    have hi_le : i ≤ m - 1 := by omega
    have hsucc_one : 1 ≤ i + 1 := by omega
    have hsucc_le : i + 1 ≤ m - 1 := by omega
    have hden_i := hden i hi hi_le
    have hden_succ := hden (i + 1) hsucc_one hsucc_le
    have hu_closed :=
      claim_13 E m alpha beta u hcoord_beta_ne_zero hcoord_recurrence_u
        hcoord_beta_characteristic_root hcoord_initial.1
        hcoord_denominator_nonzero (i + 1) hsucc_one hsucc_le
    simp only [Nat.add_sub_cancel] at hu_closed
    rw [← hcoord_tau_mul, hu_closed]
    congr 1
    calc
      ((beta ^ i + (beta⁻¹) ^ i) / alpha) ^ 2 *
          (((beta ^ i + (beta⁻¹) ^ i) /
            (beta ^ (i + 1) + (beta⁻¹) ^ (i + 1)))⁻¹) ^ 2 =
          ((beta ^ i + (beta⁻¹) ^ i) / alpha) ^ 2 *
            ((beta ^ (i + 1) + (beta⁻¹) ^ (i + 1)) /
              (beta ^ i + (beta⁻¹) ^ i)) ^ 2 := by
        rw [inv_div]
      _ = (beta ^ i + (beta⁻¹) ^ i) ^ 2 / alpha ^ 2 *
            ((beta ^ (i + 1) + (beta⁻¹) ^ (i + 1)) ^ 2 /
              (beta ^ i + (beta⁻¹) ^ i) ^ 2) := by
        rw [div_pow, div_pow]
      _ = (beta ^ (i + 1) + (beta⁻¹) ^ (i + 1)) ^ 2 / alpha ^ 2 :=
        div_mul_div_cancel₀' (pow_ne_zero 2 hden_i) _ _
      _ = ((beta ^ (i + 1) + (beta⁻¹) ^ (i + 1)) / alpha) ^ 2 := by
        rw [div_pow]
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi hle
      cases i with
      | zero => omega
      | succ j =>
          cases j with
          | zero =>
              rcases hcoord_initial with ⟨_hu1, hd1⟩
              calc
                d 1 = zeta := hd1
                _ = zeta ^ 1 *
                    tau (((beta ^ 1 + (beta⁻¹) ^ 1) / alpha) ^ 2) := by
                  simp [htau_base]
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
              have hprev := ih k hk_lt_i hk_one hk_le
              have hu_closed :=
                claim_13 E m alpha beta u hcoord_beta_ne_zero
                  hcoord_recurrence_u hcoord_beta_characteristic_root
                  hcoord_initial.1
                  hcoord_denominator_nonzero k hk_one hk_le
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
                rw [← hu_closed, huk]
                exact CharTwo.add_self_eq_zero alpha
              have hrec := hcoord_recurrence_d k hnostop
              have htau := htau_step k hk_one hk_lt
              calc
                d (k + 1) =
                    d k * zeta * tau (((u (k + 1))⁻¹) ^ 2) := hrec
                _ =
                    (zeta ^ k *
                        tau (((beta ^ k + (beta⁻¹) ^ k) / alpha) ^ 2)) *
                      zeta * tau (((u (k + 1))⁻¹) ^ 2) := by
                  rw [hprev]
                _ =
                    zeta ^ (k + 1) *
                      (tau (((beta ^ k + (beta⁻¹) ^ k) / alpha) ^ 2) *
                        tau (((u (k + 1))⁻¹) ^ 2)) := by
                  dsimp [k]
                  rw [pow_succ]
                  ring_nf
                _ =
                    zeta ^ (k + 1) *
                      tau (((beta ^ (k + 1) + (beta⁻¹) ^ (k + 1)) /
                        alpha) ^ 2) := by
                  rw [htau]

public theorem section2SequenceClosedData
    (E : Type*) [Field E] [CharP E 2] (m : ℕ) (zeta alpha beta : E)
    (tau : E → E) (u d : ℕ → E) (hcoord_beta_ne_zero : beta ≠ 0)
    (hcoord_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hcoord_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hcoord_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hcoord_initial : u 1 = 0 ∧ d 1 = zeta)
    (hcoord_alpha_ne_zero : alpha ≠ 0)
    (hcoord_tau_one : tau 1 = 1)
    (hcoord_tau_mul : ∀ x y : E, tau (x * y) = tau x * tau y)
    (hcoord_denominator_nonzero : ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
      beta ^ i + (beta⁻¹) ^ i ≠ 0) :
    Section2SequenceClosedData E m zeta alpha beta tau u d := by
  refine ⟨?_, ?_, hcoord_denominator_nonzero⟩
  · exact claim_13 E m alpha beta u hcoord_beta_ne_zero
      hcoord_recurrence_u hcoord_beta_characteristic_root hcoord_initial.1
      hcoord_denominator_nonzero
  · exact claim_14 E m zeta alpha beta tau u d hcoord_beta_ne_zero
      hcoord_recurrence_u hcoord_recurrence_d hcoord_beta_characteristic_root
      hcoord_initial hcoord_alpha_ne_zero hcoord_tau_one hcoord_tau_mul
      hcoord_denominator_nonzero

end PFchapter4section2
end CFSG.BenderSuzuki

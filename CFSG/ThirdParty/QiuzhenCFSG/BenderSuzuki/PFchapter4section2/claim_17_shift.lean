module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_15_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

/-!
# Peterfalvi, Part II, Chapter IV, Section 2, auxiliary step for Claim (17)
-/

/-- A field calculation converting a product identity into the quotient form
used in the Peterfalvi proof of claim (17). -/
public theorem claim_17_ratio_from_product
    {E : Type*} [Field E] (p a c s : E)
    (ha : a ≠ 0) (hs : s ≠ 0)
    (hps : p * s = a ^ 2 + c ^ 2) :
    p / a = (1 + (c / a) ^ 2) * (a / s) := by
  field_simp [ha, hs]
  rw [← hps]

/-- The characteristic-two beta-sum product identity behind equation (13). -/
public theorem claim_17_beta_product_identity
    {E : Type*} [Field E] [CharP E 2] (beta : E) (i : ℕ)
    (hi : 1 ≤ i) (hbeta : beta ≠ 0) :
      (beta ^ (i - 1) + (beta⁻¹) ^ (i - 1)) *
          (beta ^ (i + 1) + (beta⁻¹) ^ (i + 1)) =
        (beta ^ i + (beta⁻¹) ^ i) ^ 2 + (beta + beta⁻¹) ^ 2 := by
  cases i with
  | zero => omega
  | succ j =>
      have hpow_ne : beta ^ j ≠ 0 := pow_ne_zero j hbeta
      have hbeta2_ne : beta ^ 2 ≠ 0 := pow_ne_zero 2 hbeta
      simp
      ring_nf
      simp [CharTwo.two_eq_zero]
      field_simp [hpow_ne, hbeta2_ne]

/-- The closed beta-sum ratio identity used to rewrite `u_i / u_{i+1}`. -/
public theorem claim_17_beta_ratio_identity
    {E : Type*} [Field E] [CharP E 2] (beta : E) (i : ℕ)
    (hi : 1 ≤ i) (hbeta : beta ≠ 0)
    (hden_i : beta ^ i + (beta⁻¹) ^ i ≠ 0)
    (hden_succ : beta ^ (i + 1) + (beta⁻¹) ^ (i + 1) ≠ 0) :
    (beta ^ (i - 1) + (beta⁻¹) ^ (i - 1)) /
        (beta ^ i + (beta⁻¹) ^ i) =
      (1 + ((beta + beta⁻¹) / (beta ^ i + (beta⁻¹) ^ i)) ^ 2) *
        ((beta ^ i + (beta⁻¹) ^ i) /
          (beta ^ (i + 1) + (beta⁻¹) ^ (i + 1))) := by
  exact
    claim_17_ratio_from_product
      (beta ^ (i - 1) + (beta⁻¹) ^ (i - 1))
      (beta ^ i + (beta⁻¹) ^ i)
      (beta + beta⁻¹)
      (beta ^ (i + 1) + (beta⁻¹) ^ (i + 1))
      hden_i hden_succ
      (claim_17_beta_product_identity beta i hi hbeta)

/-- In characteristic two, the characteristic-root equation identifies
`alpha` with the basic beta sum. -/
public theorem claim_17_alpha_eq_beta_add_inv
    {E : Type*} [Field E] [CharP E 2] {alpha beta : E}
    (hbeta : beta ≠ 0)
    (hroot : beta ^ 2 + alpha * beta + 1 = 0) :
    alpha = beta + beta⁻¹ := by
  exact alpha_eq_beta_add_inv_of_characteristic_root hbeta hroot

/--
The closed-form calculation for the ratio `u_i / u_{i+1}` coming from Peterfalvi
equation (13), written in multiplied form.
-/
public theorem claim_17_u_closed_form_ratio
    {E : Type*} [Field E] [CharP E 2]
    (m : ℕ) (zeta alpha beta : E) (sigma tau : E → E)
    (u d : ℕ → E)
    (hseq_zeta_ne_one : zeta ≠ 1) (hseq_alpha_ne_zero : alpha ≠ 0)
    (hseq_beta_ne_zero : beta ≠ 0) (hseq_tau_nonzero : ∀ x : E, x ≠ 0 → tau x ≠ 0)
    (hseq_zeta_order : orderOf zeta = m)
    (hseq_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hseq_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hseq_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hseq_closed : Section2SequenceClosedData E m zeta alpha beta tau u d) :
    ∀ i : ℕ, 1 ≤ i → i < m - 1 →
      u i =
        (1 + ((beta + beta⁻¹) / (beta ^ i + (beta⁻¹) ^ i)) ^ 2) *
          u (i + 1) := by
  have _ := sigma
  have _ := hseq_zeta_ne_one
  have _ := hseq_alpha_ne_zero
  have _ := hseq_tau_nonzero
  have _ := hseq_zeta_order
  have _ := hseq_recurrence_u
  have _ := hseq_recurrence_d
  have _ := hseq_beta_characteristic_root
  intro i hi hlt
  have hle : i ≤ m - 1 := by omega
  have hsucc_le : i + 1 ≤ m - 1 := by omega
  have hsucc_one : 1 ≤ i + 1 := by omega
  have hden_i := hseq_closed.denominator_nonzero i hi hle
  have hden_succ :=
    hseq_closed.denominator_nonzero (i + 1) hsucc_one hsucc_le
  rw [hseq_closed.u_closed i hi hle,
    hseq_closed.u_closed (i + 1) hsucc_one hsucc_le]
  exact claim_17_beta_ratio_identity beta i hi hseq_beta_ne_zero hden_i hden_succ

/--
The closed-form calculation for `d_i^{-(1+sigma)}` coming from Peterfalvi equation
(14), aligned with the ratio used in claim (17).
-/
public theorem claim_17_d_sigma_inverse
    {E : Type*} [Field E] [CharP E 2]
    (m : ℕ) (zeta alpha beta : E) (sigma tau : E → E)
    (u d : ℕ → E)
    (hseq_zeta_ne_one : zeta ≠ 1) (hseq_alpha_ne_zero : alpha ≠ 0)
    (hseq_beta_ne_zero : beta ≠ 0) (hseq_tau_nonzero : ∀ x : E, x ≠ 0 → tau x ≠ 0)
    (hseq_zeta_order : orderOf zeta = m)
    (hseq_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hseq_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hseq_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hseq_closed : Section2SequenceClosedData E m zeta alpha beta tau u d)
    (hdprod :
      ∀ i : ℕ, 1 ≤ i → i < m - 1 →
        d i * sigma (d i) = ((beta ^ i + (beta⁻¹) ^ i) / alpha) ^ 2) :
    ∀ i : ℕ, 1 ≤ i → i < m - 1 →
      (d i * sigma (d i))⁻¹ =
        ((beta + beta⁻¹) / (beta ^ i + (beta⁻¹) ^ i)) ^ 2 := by
  have _ := hseq_zeta_ne_one
  have _ := hseq_tau_nonzero
  have _ := hseq_zeta_order
  have _ := hseq_recurrence_u
  have _ := hseq_recurrence_d
  intro i hi hlt
  have hle : i ≤ m - 1 := by omega
  have hden := hseq_closed.denominator_nonzero i hi hle
  have halpha :=
    claim_17_alpha_eq_beta_add_inv
      hseq_beta_ne_zero hseq_beta_characteristic_root
  rw [hdprod i hi hlt, ← halpha]
  field_simp [hseq_alpha_ne_zero, hden]

/--
Closed-form ratio calculation from Peterfalvi equations (13) and (14), rewritten
without division by `u_{i+1}`.
-/
public theorem claim_17_closed_form_step
    {E : Type*} [Field E] [CharP E 2]
    (m n : ℕ) (zeta alpha beta : E) (theta sigma tau : E → E)
    (u v d : ℕ → E)
    (hcoord_zeta_ne_one : zeta ≠ 1) (hcoord_beta_ne_zero : beta ≠ 0)
    (hcoord_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hcoord_recurrence_v : ∀ i : ℕ, u i ≠ alpha →
      v (i + 1) = v i + u (i + 1) * (d i * sigma (d i))⁻¹)
    (hcoord_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hcoord_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hseq_zeta_ne_one : zeta ≠ 1) (hseq_alpha_ne_zero : alpha ≠ 0)
    (hseq_beta_ne_zero : beta ≠ 0) (hseq_tau_nonzero : ∀ x : E, x ≠ 0 → tau x ≠ 0)
    (hseq_zeta_order : orderOf zeta = m)
    (hseq_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hseq_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hseq_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hseq_closed : Section2SequenceClosedData E m zeta alpha beta tau u d)
    (hdprod :
      ∀ i : ℕ, 1 ≤ i → i < m - 1 →
        d i * sigma (d i) = ((beta ^ i + (beta⁻¹) ^ i) / alpha) ^ 2) :
    ∀ i : ℕ, 1 ≤ i → i < m - 1 →
      u i = (1 + (d i * sigma (d i))⁻¹) * u (i + 1) := by
  have _ := n
  have _ := theta
  have _ := hcoord_zeta_ne_one
  have _ := hcoord_beta_ne_zero
  have _ := hcoord_recurrence_u
  have _ := hcoord_recurrence_v
  have _ := hcoord_recurrence_d
  have _ := hcoord_beta_characteristic_root
  intro i hi hlt
  rw [claim_17_d_sigma_inverse m zeta alpha beta sigma tau u d
    hseq_zeta_ne_one hseq_alpha_ne_zero hseq_beta_ne_zero hseq_tau_nonzero
    hseq_zeta_order hseq_recurrence_u hseq_recurrence_d
    hseq_beta_characteristic_root hseq_closed hdprod i hi hlt]
  exact claim_17_u_closed_form_ratio m zeta alpha beta sigma tau u d
    hseq_zeta_ne_one hseq_alpha_ne_zero hseq_beta_ne_zero hseq_tau_nonzero
    hseq_zeta_order hseq_recurrence_u hseq_recurrence_d
    hseq_beta_characteristic_root hseq_closed i hi hlt

/--
The explicit ratio calculation used in the proof of claim (17), corresponding
to the Peterfalvi identity `u_i / u_{i+1} = 1 + d_i^{-(1+sigma)}`.
-/
public theorem claim_17_step_relation
    {E : Type*} [Field E] [CharP E 2]
    (m n : ℕ) (zeta alpha beta : E) (theta sigma tau : E → E)
    (u v d : ℕ → E)
    (hcoord_zeta_ne_one : zeta ≠ 1) (hcoord_beta_ne_zero : beta ≠ 0)
    (hcoord_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hcoord_recurrence_v : ∀ i : ℕ, u i ≠ alpha →
      v (i + 1) = v i + u (i + 1) * (d i * sigma (d i))⁻¹)
    (hcoord_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hcoord_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hseq_zeta_ne_one : zeta ≠ 1) (hseq_alpha_ne_zero : alpha ≠ 0)
    (hseq_beta_ne_zero : beta ≠ 0) (hseq_tau_nonzero : ∀ x : E, x ≠ 0 → tau x ≠ 0)
    (hseq_zeta_order : orderOf zeta = m)
    (hseq_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hseq_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hseq_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hseq_closed : Section2SequenceClosedData E m zeta alpha beta tau u d)
    (hdprod :
      ∀ i : ℕ, 1 ≤ i → i < m - 1 →
        d i * sigma (d i) = ((beta ^ i + (beta⁻¹) ^ i) / alpha) ^ 2) :
    ∀ i : ℕ, 1 ≤ i → i < m - 1 →
      u (i + 1) * (d i * sigma (d i))⁻¹ + u (i + 1) = u i := by
  intro i hi hlt
  rw [claim_17_closed_form_step m n zeta alpha beta theta sigma tau u v d
    hcoord_zeta_ne_one hcoord_beta_ne_zero hcoord_recurrence_u
    hcoord_recurrence_v hcoord_recurrence_d hcoord_beta_characteristic_root
    hseq_zeta_ne_one hseq_alpha_ne_zero hseq_beta_ne_zero hseq_tau_nonzero
    hseq_zeta_order hseq_recurrence_u hseq_recurrence_d
    hseq_beta_characteristic_root hseq_closed hdprod i hi hlt]
  ring

/--
The Peterfalvi proof of claim (17) first proves that `v_i + u_i = alpha` from the
recurrences and closed forms. In characteristic two this is the coordinate
shift `v_i = u_i + alpha` used to rewrite the selected sequence formula.
-/
public theorem claim_17_v_plus_u
    {E : Type*} [Field E] [CharP E 2]
    (m n : ℕ) (zeta alpha beta : E) (theta sigma tau : E → E)
    (u v d : ℕ → E)
    (hcoord_zeta_ne_one : zeta ≠ 1) (hcoord_beta_ne_zero : beta ≠ 0)
    (hcoord_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hcoord_recurrence_v : ∀ i : ℕ, u i ≠ alpha →
      v (i + 1) = v i + u (i + 1) * (d i * sigma (d i))⁻¹)
    (hcoord_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hcoord_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hcoord_initial : u 1 = 0 ∧ v 1 = alpha ∧ d 1 = zeta)
    (hseq_zeta_ne_one : zeta ≠ 1) (hseq_alpha_ne_zero : alpha ≠ 0)
    (hseq_beta_ne_zero : beta ≠ 0) (hseq_tau_nonzero : ∀ x : E, x ≠ 0 → tau x ≠ 0)
    (hseq_zeta_order : orderOf zeta = m)
    (hseq_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hseq_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hseq_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hseq_closed : Section2SequenceClosedData E m zeta alpha beta tau u d)
    (hdprod :
      ∀ i : ℕ, 1 ≤ i → i < m - 1 →
        d i * sigma (d i) = ((beta ^ i + (beta⁻¹) ^ i) / alpha) ^ 2) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 → v i + u i = alpha := by
  intro i
  induction i with
  | zero =>
      intro hi _him
      omega
  | succ i ih =>
      intro _hi him
      cases i with
      | zero =>
          rcases hcoord_initial with
            ⟨hu1, hv1, _hd1⟩
          simp [hu1, hv1]
      | succ j =>
          have hprev_le : Nat.succ j ≤ m - 1 := by omega
          have hprev_lt : Nat.succ j < m - 1 := by omega
          have hprev_one : 1 ≤ Nat.succ j := by omega
          have hprev := ih hprev_one hprev_le
          have hnostop :=
            (claim_15_a E m zeta alpha beta tau u d sigma
              hseq_zeta_ne_one hseq_alpha_ne_zero hseq_beta_ne_zero
              hseq_tau_nonzero hseq_zeta_order hseq_recurrence_u
              hseq_recurrence_d hseq_beta_characteristic_root hseq_closed).1
              (Nat.succ j) hprev_one hprev_lt
          have hvrec := hcoord_recurrence_v (Nat.succ j) hnostop
          have hstep :=
            claim_17_step_relation m n zeta alpha beta theta sigma tau u v d
              hcoord_zeta_ne_one hcoord_beta_ne_zero hcoord_recurrence_u
              hcoord_recurrence_v hcoord_recurrence_d
              hcoord_beta_characteristic_root hseq_zeta_ne_one
              hseq_alpha_ne_zero hseq_beta_ne_zero hseq_tau_nonzero
              hseq_zeta_order hseq_recurrence_u hseq_recurrence_d
              hseq_beta_characteristic_root hseq_closed hdprod
              (Nat.succ j) hprev_one hprev_lt
          rw [hvrec]
          calc
            (v (Nat.succ j) +
                u (Nat.succ j + 1) *
                  (d (Nat.succ j) * sigma (d (Nat.succ j)))⁻¹) +
                u (Nat.succ j + 1)
                = v (Nat.succ j) +
                    (u (Nat.succ j + 1) *
                        (d (Nat.succ j) * sigma (d (Nat.succ j)))⁻¹ +
                      u (Nat.succ j + 1)) := by
                  ring
            _ = v (Nat.succ j) + u (Nat.succ j) := by rw [hstep]
            _ = alpha := hprev

/-- Coordinate-shift form of `claim_17_v_plus_u`, separated as the last rewrite
used by claim (17). -/
public theorem claim_17_v_eq_shift
    {E : Type*} [Field E] [CharP E 2]
    (m n : ℕ) (zeta alpha beta : E) (theta sigma tau : E → E)
    (u v d : ℕ → E)
    (hcoord_zeta_ne_one : zeta ≠ 1) (hcoord_beta_ne_zero : beta ≠ 0)
    (hcoord_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hcoord_recurrence_v : ∀ i : ℕ, u i ≠ alpha →
      v (i + 1) = v i + u (i + 1) * (d i * sigma (d i))⁻¹)
    (hcoord_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hcoord_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hcoord_initial : u 1 = 0 ∧ v 1 = alpha ∧ d 1 = zeta)
    (hseq_zeta_ne_one : zeta ≠ 1) (hseq_alpha_ne_zero : alpha ≠ 0)
    (hseq_beta_ne_zero : beta ≠ 0) (hseq_tau_nonzero : ∀ x : E, x ≠ 0 → tau x ≠ 0)
    (hseq_zeta_order : orderOf zeta = m)
    (hseq_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hseq_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hseq_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hseq_closed : Section2SequenceClosedData E m zeta alpha beta tau u d)
    (hdprod :
      ∀ i : ℕ, 1 ≤ i → i < m - 1 →
        d i * sigma (d i) = ((beta ^ i + (beta⁻¹) ^ i) / alpha) ^ 2) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 → v i = u i + alpha := by
  intro i hi him
  rw [← claim_17_v_plus_u m n zeta alpha beta theta sigma tau u v d
    hcoord_zeta_ne_one hcoord_beta_ne_zero hcoord_recurrence_u
    hcoord_recurrence_v hcoord_recurrence_d hcoord_beta_characteristic_root
    hcoord_initial hseq_zeta_ne_one hseq_alpha_ne_zero hseq_beta_ne_zero
    hseq_tau_nonzero hseq_zeta_order hseq_recurrence_u hseq_recurrence_d
    hseq_beta_characteristic_root hseq_closed hdprod i hi him]
  rw [add_comm (v i) (u i)]
  exact (CharTwo.add_cancel_left (u i) (v i)).symm

end PFchapter4section2
end CFSG.BenderSuzuki

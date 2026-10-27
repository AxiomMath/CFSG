module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_14

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (15)(a) -/

public theorem claim_15_a
    (E : Type*) [Field E] [CharP E 2] (m : ℕ) (zeta alpha beta : E)
    (tau : E → E) (u d : ℕ → E)
    (_ : E → E) (_ : zeta ≠ 1) (hseq_alpha_ne_zero : alpha ≠ 0)
    (hseq_beta_ne_zero : beta ≠ 0) (hseq_tau_nonzero : ∀ x : E, x ≠ 0 → tau x ≠ 0)
    (hseq_zeta_order : orderOf zeta = m)
    (_ : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (_ : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hseq_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hseq_closed : Section2SequenceClosedData E m zeta alpha beta tau u d) :
    (∀ i : ℕ, 1 ≤ i → i < m - 1 → u i ≠ alpha) ∧
      (∀ i : ℕ, 1 ≤ i → i ≤ m - 1 → d i ≠ 0) := by
  have halpha : alpha = beta + beta⁻¹ :=
    alpha_eq_beta_add_inv_of_characteristic_root
      hseq_beta_ne_zero hseq_beta_characteristic_root
  constructor
  · intro i hi hlt hui
    have hle : i ≤ m - 1 := by omega
    have hsucc_one : 1 ≤ i + 1 := by omega
    have hsucc_le : i + 1 ≤ m - 1 := by omega
    have hclosed := hseq_closed.u_closed i hi hle
    have hden_i := hseq_closed.denominator_nonzero i hi hle
    have hden_succ :=
      hseq_closed.denominator_nonzero (i + 1) hsucc_one hsucc_le
    have hstep :=
      claim_13_beta_sum_step hseq_beta_ne_zero halpha i hi hden_i hden_succ
    have hsum_ne :
        alpha +
            (beta ^ (i - 1) + (beta⁻¹) ^ (i - 1)) /
              (beta ^ i + (beta⁻¹) ^ i) ≠ 0 := by
      intro hzero
      have hquot_zero :
          (beta ^ i + (beta⁻¹) ^ i) /
              (beta ^ (i + 1) + (beta⁻¹) ^ (i + 1)) = 0 := by
        rw [← hstep]
        simpa [inv_pow] using hzero
      exact (div_ne_zero hden_i hden_succ) hquot_zero
    apply hsum_ne
    rw [← hclosed, hui]
    exact CharTwo.add_self_eq_zero alpha
  · intro i hi hle
    have hzeta_ne_zero : zeta ≠ 0 := by
      intro hzeta
      have horder_zero : orderOf zeta = 0 := by
        simp [hzeta]
      have hm_zero : m = 0 := by
        rw [← hseq_zeta_order, horder_zero]
      omega
    rw [hseq_closed.d_closed i hi hle]
    apply mul_ne_zero
    · exact pow_ne_zero i hzeta_ne_zero
    · apply hseq_tau_nonzero
      apply pow_ne_zero
      exact div_ne_zero (hseq_closed.denominator_nonzero i hi hle)
        hseq_alpha_ne_zero

end PFchapter4section2
end CFSG.BenderSuzuki

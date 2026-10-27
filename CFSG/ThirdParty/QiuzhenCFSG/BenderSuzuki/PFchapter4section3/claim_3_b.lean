module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section3.claim_3_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section3

/-! # Peterfalvi, Part II, Chapter IV, Section 3, Claim (3)(b) -/

/-- The final coordinate identification in Claim (3).  After `theta = 1`,
Peterfalvi's equation `(*)` reduces to `alpha² + beta² = 0`; injectivity of
the squaring map in a field gives `alpha = beta`. -/
public theorem claim_3_b
    {F : Type*} [Field F] [CharP F 2]
    (theta : F ≃+* F) (alpha beta X : F)
    (htheta : theta = 1)
    (hidentity :
      alpha ^ 2 + beta ^ 2 + beta * (X + theta X) = 0) :
    alpha = beta := by
  rw [htheta] at hidentity
  have hsq : alpha ^ 2 + beta ^ 2 = 0 := by
    simpa [CharTwo.add_self_eq_zero] using hidentity
  have hsum_sq : (alpha + beta) ^ 2 = 0 := by
    rw [CharTwo.add_sq, hsq]
  exact CharTwo.add_eq_zero.mp (eq_zero_of_pow_eq_zero hsum_sq)

/-- Cross-multiplication in the displayed fraction equation of Claim (3). -/
public theorem claim_3_rational_step
    {E : Type*} [Field E] [CharP E 2]
    (a b zeta : E) (ha : a ≠ 0) (hzeta : zeta ≠ 0)
    (hdena : a ^ 2 + zeta⁻¹ ≠ 0)
    (hdenb : b ^ 2 + zeta⁻¹ ≠ 0)
    (hratio :
      1 / (a ^ 2 + zeta⁻¹) =
        zeta * a⁻¹ ^ 2 / (b ^ 2 + zeta⁻¹)) :
    b ^ 2 = zeta + zeta⁻¹ + a⁻¹ ^ 2 := by
  have hcross := (div_eq_div_iff hdena hdenb).mp hratio
  field_simp [ha, hzeta] at hcross ⊢
  have htwo : a ^ 2 * (2 : E) = 0 := by
    have htwoE : (2 : E) = 0 := CharTwo.two_eq_zero
    rw [htwoE, mul_zero]
  linear_combination hcross - htwo

/-- Squaring the norm equation and substituting the preceding rational step
gives Peterfalvi's equation `(*)`. -/
public theorem claim_3_norm_step
    {F : Type*} [Field F] [CharP F 2]
    (theta : F ≃+* F) (alpha beta a b : F)
    (hnorm : b * theta b = alpha + a⁻¹ * theta a⁻¹)
    (hb_sq : b ^ 2 = beta + a⁻¹ ^ 2)
    (htheta_beta : theta beta = beta) :
    alpha ^ 2 + beta ^ 2 +
        beta * (a⁻¹ ^ 2 + theta (a⁻¹ ^ 2)) = 0 := by
  have heq :
      (beta + a⁻¹ ^ 2) * (beta + theta (a⁻¹ ^ 2)) =
        alpha ^ 2 + a⁻¹ ^ 2 * theta (a⁻¹ ^ 2) := by
    calc
      (beta + a⁻¹ ^ 2) * (beta + theta (a⁻¹ ^ 2)) =
          (beta + a⁻¹ ^ 2) * theta (beta + a⁻¹ ^ 2) := by
        rw [map_add, htheta_beta]
      _ = b ^ 2 * theta (b ^ 2) := by rw [hb_sq]
      _ = (b * theta b) ^ 2 := by rw [mul_pow, map_pow]
      _ = (alpha + a⁻¹ * theta a⁻¹) ^ 2 := by rw [hnorm]
      _ = alpha ^ 2 + a⁻¹ ^ 2 * theta (a⁻¹ ^ 2) := by
        rw [CharTwo.add_sq, mul_pow, map_pow]
  have heq' :
      (beta ^ 2 + beta * (a⁻¹ ^ 2 + theta (a⁻¹ ^ 2))) +
          a⁻¹ ^ 2 * theta (a⁻¹ ^ 2) =
        alpha ^ 2 + a⁻¹ ^ 2 * theta (a⁻¹ ^ 2) := by
    calc
      (beta ^ 2 + beta * (a⁻¹ ^ 2 + theta (a⁻¹ ^ 2))) +
          a⁻¹ ^ 2 * theta (a⁻¹ ^ 2) =
        (beta + a⁻¹ ^ 2) * (beta + theta (a⁻¹ ^ 2)) := by ring
      _ = _ := heq
  have hcore :
      beta ^ 2 + beta * (a⁻¹ ^ 2 + theta (a⁻¹ ^ 2)) = alpha ^ 2 :=
    add_right_cancel heq'
  calc
    alpha ^ 2 + beta ^ 2 + beta * (a⁻¹ ^ 2 + theta (a⁻¹ ^ 2)) =
        (beta ^ 2 + beta * (a⁻¹ ^ 2 + theta (a⁻¹ ^ 2))) +
          beta ^ 2 + beta * (a⁻¹ ^ 2 + theta (a⁻¹ ^ 2)) := by rw [hcore]
    _ = (beta ^ 2 + beta ^ 2) +
        (beta * (a⁻¹ ^ 2 + theta (a⁻¹ ^ 2)) +
          beta * (a⁻¹ ^ 2 + theta (a⁻¹ ^ 2))) := by ring
    _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]


end PFchapter4section3
end CFSG.BenderSuzuki

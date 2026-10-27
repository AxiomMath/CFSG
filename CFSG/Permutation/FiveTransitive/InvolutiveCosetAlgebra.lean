module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG

namespace FiveTransitive.InvolutiveCosetAlgebra

variable {G : Type*} [Group G] (Q : Subgroup G) (x : G)

private theorem square_eq_one (h : ∀ q ∈ Q, (q * x) ^ 2 = 1) : x ^ 2 = 1 := by
  simpa using h 1 Q.one_mem

private theorem conjugate_eq_inv (h : ∀ q ∈ Q, (q * x) ^ 2 = 1)
    {q : G} (hq : q ∈ Q) : x * q * x⁻¹ = q⁻¹ := by
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using square_eq_one Q x h)
  apply mul_left_cancel (a := q)
  rw [mul_inv_cancel, hx]
  simpa [pow_two, mul_assoc] using h q hq

theorem mul_comm (h : ∀ q ∈ Q, (q * x) ^ 2 = 1)
    {q r : G} (hq : q ∈ Q) (hr : r ∈ Q) : q * r = r * q := by
  have hc : q⁻¹ * r⁻¹ = r⁻¹ * q⁻¹ := by
    calc
      q⁻¹ * r⁻¹ = (x * q * x⁻¹) * (x * r * x⁻¹) := by
        rw [conjugate_eq_inv Q x h hq, conjugate_eq_inv Q x h hr]
      _ = x * (q * r) * x⁻¹ := by simp [mul_assoc]
      _ = (q * r)⁻¹ := conjugate_eq_inv Q x h (Q.mul_mem hq hr)
      _ = r⁻¹ * q⁻¹ := mul_inv_rev q r
  simpa using congrArg Inv.inv hc.symm

theorem commute_iff_square_eq_one (h : ∀ q ∈ Q, (q * x) ^ 2 = 1)
    {q : G} (hq : q ∈ Q) : Commute q x ↔ q ^ 2 = 1 := by
  have hi := conjugate_eq_inv Q x h hq
  constructor
  · intro hc
    have he : q = q⁻¹ := by
      calc
        q = x * q * x⁻¹ := by rw [← hc.eq]; simp
        _ = q⁻¹ := hi
    calc
      q ^ 2 = q⁻¹ * q := by rw [pow_two]; exact congrArg (fun z => z * q) he
      _ = 1 := inv_mul_cancel q
  · intro hq2
    have he : q⁻¹ = q := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hq2)
    rw [he] at hi
    have heq := congrArg (fun z : G => z * x) hi
    exact (show x * q = q * x by simpa [mul_assoc] using heq).symm

end FiveTransitive.InvolutiveCosetAlgebra

end CFSG

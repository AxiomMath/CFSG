module

public import CFSG.Monster.VisQuot.Monomial

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot

theorem permAct_ofAdd (p : AutPerm) (y : C ⧸ ΩLine) :
    permAct p (Multiplicative.ofAdd y) = Multiplicative.ofAdd (permQ p y) := rfl

theorem inl_conj (e x : C ⧸ ΩLine) (p : AutPerm) :
    (SemidirectProduct.inl (Multiplicative.ofAdd e) : MonoSD) * ⟨Multiplicative.ofAdd x, p⟩ *
      (SemidirectProduct.inl (Multiplicative.ofAdd e))⁻¹ =
      ⟨Multiplicative.ofAdd (x + e + permQ p e), p⟩ := by
  refine SemidirectProduct.ext ?_ ?_
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, inv_one, map_one, MulAut.one_apply]
    rw [← ofAdd_neg, permAct_ofAdd, ← ofAdd_add, ← ofAdd_add, map_neg, ZModModule.neg_eq_self]
    congr 1
    abel
  · simp

theorem inr_conj (c : AutPerm) (x : C ⧸ ΩLine) (p : AutPerm) :
    (SemidirectProduct.inr c : MonoSD) * ⟨Multiplicative.ofAdd x, p⟩ *
      (SemidirectProduct.inr c)⁻¹ = ⟨Multiplicative.ofAdd (permQ c x), c * p * c⁻¹⟩ := by
  refine SemidirectProduct.ext ?_ ?_
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, inv_one, map_one, one_mul, mul_one]
    rfl
  · simp

theorem mul_self_eq_one_iff (x : C ⧸ ΩLine) (p : AutPerm) :
    (⟨Multiplicative.ofAdd x, p⟩ : MonoSD) * ⟨Multiplicative.ofAdd x, p⟩ = 1 ↔
      p * p = 1 ∧ x + permQ p x = 0 := by
  rw [SemidirectProduct.ext_iff]
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.one_left,
    SemidirectProduct.one_right, permAct_ofAdd, ← ofAdd_add]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, Multiplicative.ofAdd.injective h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h2]; rfl, h1⟩

end CFSG.Monster.B.TwoA.Census

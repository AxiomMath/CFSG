module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG

namespace FiveTransitive.CoprimeAutomorphismDisplacement

private theorem eq_one
    {G : Type*} [Group G] (N : Subgroup G) [Finite N]
    (a : MulAut G) (k : ℕ) (hak : a ^ k = 1)
    (hcop : k.Coprime (Nat.card N))
    (hfix : ∀ z ∈ N, a z = z)
    (hdisp : ∀ x : G, x⁻¹ * a x ∈ N) : a = 1 := by
  apply MulEquiv.ext
  intro x
  let z := x⁻¹ * a x
  have hzN : z ∈ N := hdisp x
  have hz : a z = z := hfix z hzN
  have hx : a x = x * z := by simp [z]
  have hi (n : ℕ) : (a ^ n) x = x * z ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',MulAut.mul_apply,ih,map_mul,map_pow,hz,hx,mul_assoc,← pow_succ']
  have hzk : z ^ k = 1 := by
    apply mul_left_cancel (a := x)
    rw [← hi,hak]
    simp
  have hzk' : (⟨z,hzN⟩ : N) ^ k = 1 := Subtype.ext hzk
  have hzOne : (⟨z,hzN⟩ : N) = 1 :=
    (pow_eq_one_iff_of_coprime hcop).mp ⟨hzk',pow_card_eq_one'⟩
  have hzVal : z = 1 := congrArg Subtype.val hzOne
  simpa only [hzVal,mul_one,MulAut.one_apply] using hx

theorem eq_one_of_quotient
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [Finite N]
    (a : MulAut G) (k : ℕ) (hak : a ^ k = 1)
    (hcop : k.Coprime (Nat.card N))
    (hfix : ∀ z ∈ N, a z = z)
    (hquot : ∀ x : G, (QuotientGroup.mk' N) (a x) = (QuotientGroup.mk' N) x) :
    a = 1 := by
  apply eq_one N a k hak hcop hfix
  intro x
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' N) (x⁻¹ * a x) = 1
  rw [map_mul,map_inv,hquot]
  simp

end FiveTransitive.CoprimeAutomorphismDisplacement

end CFSG

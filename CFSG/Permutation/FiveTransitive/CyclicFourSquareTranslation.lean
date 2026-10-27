module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.CyclicFourSquareTranslation

open MulAction

private theorem square_cases {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 4) (b : H) (hb : orderOf b = 4)
    (q : H) (hq : q ^ 2 = 1) : q = 1 ∨ q = b ^ 2 := by
  let e : Fin 4 → H := fun i => b ^ i.val
  have hinj : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have hm := pow_inj_mod.mp hij
    simpa only [hb, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hm
  have hbij : Function.Bijective e := hinj.bijective_of_nat_card_le (by rw [hH]; simp)
  obtain ⟨i, rfl⟩ := hbij.surjective q
  have hd : 4 ∣ i.val * 2 := by
    have hp : b ^ (i.val * 2) = 1 := by rw [pow_mul]; exact hq
    simpa only [hb] using orderOf_dvd_of_pow_eq_one hp
  fin_cases i
  · exact Or.inl (by simp [e])
  · norm_num at hd
  · exact Or.inr rfl
  · norm_num at hd

theorem orbit_action_cases
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 4) (b : Q) (hb : orderOf b = 4)
    (hQcomm : ∀ q r : Q, Commute q.val r.val)
    (z : G) (hz : z ^ 2 = 1) (hcomm : ∀ q : Q, Commute q.val z)
    (w : X) (hfree : ∀ q : Q, q • w = w → q = 1)
    (hstable : z • w ∈ orbit Q w) :
    (∀ t ∈ orbit Q w, z • t = t) ∨
      (∀ t ∈ orbit Q w, z • t = b.val ^ 2 • t) := by
  obtain ⟨q, hqw⟩ := mem_orbit_iff.mp hstable
  change q.val • w = z • w at hqw
  have hq2 : q ^ 2 = 1 := hfree (q ^ 2) (by
    change (q.val ^ 2) • w = w
    rw [pow_two, mul_smul, hqw, ← mul_smul, (hcomm q).eq, mul_smul, hqw,
      ← mul_smul, ← pow_two, hz, one_smul])
  have htranslation : ∀ t ∈ orbit Q w, z • t = q.val • t := by
    intro t ht
    obtain ⟨r, rfl⟩ := mem_orbit_iff.mp ht
    change z • (r.val • w) = q.val • (r.val • w)
    rw [← mul_smul, ← (hcomm r).eq, mul_smul, ← hqw,
      ← mul_smul, (hQcomm r q).eq, mul_smul]
  rcases square_cases hQ b hb q hq2 with h | h
  · left
    intro t ht
    simpa only [h, OneMemClass.coe_one, one_smul] using htranslation t ht
  · right
    intro t ht
    simpa only [h, Subgroup.coe_pow] using htranslation t ht

end FiveTransitive.CyclicFourSquareTranslation

end CFSG

module

public import CFSG.Permutation.FiveTransitive.NilpotentHomCardBound
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG

namespace FiveTransitive.ExponentTwoOrderEight

theorem exists_order_eight_in_coset
    (G : Type*) [Group G] (Q : Subgroup G) [Finite Q]
    (hcomm : ∀ q r : Q, q * r = r * q) (h2 : ∀ q : Q, q * q = 1)
    (hcard : Nat.card Q = 16) (a : G) (haN : a ∈ Subgroup.normalizer (Q : Set G))
    (ha4 : a ^ 4 = 1)
    (hfix : Nat.card {q : Q // Q.normalizerMonoidHom ⟨a, haN⟩ q = q} = 2) :
    ∃ q : Q, orderOf ((q : G) * a) = 8 := by
  let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hcomm }
  let f : Q →* Q := (Q.normalizerMonoidHom ⟨a, haN⟩).toMonoidHom
  let d : Q →* Q := f * MonoidHom.id Q
  have hd (q : Q) : d q = f q * q := rfl
  have hfval (q : Q) : (f q : G) = a * (q : G) * a⁻¹ :=
    Q.normalizerMonoidHom_apply_apply_coe ⟨a, haN⟩ q
  have hker (q : Q) : q ∈ d.ker ↔ f q = q := by
    change f q * q = 1 ↔ f q = q
    constructor
    · intro h
      apply mul_right_cancel (b := q)
      exact h.trans (h2 q).symm
    · intro h
      rw [h, h2]
  have hkerCard : Nat.card d.ker = 2 := by
    calc
      Nat.card d.ker = Nat.card {q : Q // f q = q} := Nat.card_congr
        { toFun := fun q => ⟨q.val, (hker q).mp q.property⟩
          invFun := fun q => ⟨q.val, (hker q).mpr q.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      _ = 2 := hfix
  have hnorm (q : Q) : ((q : G) * a) ^ 4 = (d (d (d q)) : G) := by
    have hd3 : d (d (d q)) = q * f q * f (f q) * f (f (f q)) := by
      calc
        d (d (d q)) = (q * f q * f (f q) * f (f (f q))) *
            ((f (f q) * f (f q)) * (f q * f q)) := by
          simp only [hd, map_mul]
          ac_rfl
        _ = q * f q * f (f q) * f (f (f q)) := by rw [h2, h2]; simp
    calc
      ((q : G) * a) ^ 4 = (q : G) * (f q : G) * (f (f q) : G) * (f (f (f q)) : G) * a ^ 4 := by
        simp only [hfval, pow_succ, pow_zero]
        group
      _ = (q : G) * (f q : G) * (f (f q) : G) * (f (f (f q)) : G) := by rw [ha4, mul_one]
      _ = (d (d (d q)) : G) := (congrArg Subtype.val hd3).symm
  obtain ⟨q, hq⟩ : ∃ q : Q, d (d (d q)) ≠ 1 := by
    by_contra hn
    push Not at hn
    have h := NilpotentHomCardBound.card_le_ker_cube Q d hn
    rw [hcard, hkerCard] at h
    norm_num at h
  have hfour : ((q : G) * a) ^ 4 ≠ 1 := by
    rw [hnorm]
    intro h
    exact hq (Subtype.ext h)
  have height : ((q : G) * a) ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, hnorm, pow_two]
    exact congrArg Subtype.val (h2 (d (d (d q))))
  exact ⟨q, orderOf_eq_prime_pow (p := 2) (n := 2) hfour height⟩

end FiveTransitive.ExponentTwoOrderEight

end CFSG

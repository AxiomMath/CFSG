module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.ElementarySylowOrders

theorem four_not_dvd_orderOf
    (H : Type*) [Group H] [Finite H] (S : Sylow 2 H)
    (hS : ∀ q : S, q * q = 1) (h : H) :
    ¬ 4 ∣ orderOf h := by
  intro hd
  let u := h ^ (orderOf h / 4)
  have hu : orderOf u = 4 := orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos h)) hd
  have hcyc : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu]; norm_num)
  obtain ⟨T, hT⟩ := hcyc.exists_le_sylow
  let z : T := ⟨u, hT (Subgroup.mem_zpowers u)⟩
  let e : T ≃* S := Sylow.equiv T S
  have hz : z * z = 1 := e.injective (by
    rw [map_mul, map_one]
    exact hS (e z))
  have hupow : u ^ 2 = 1 := by
    have hval := congrArg (fun z : T => (z : H)) hz
    change u * u = 1 at hval
    simpa only [pow_two] using hval
  have hdiv := orderOf_dvd_of_pow_eq_one hupow
  rw [hu] at hdiv
  norm_num at hdiv

end FiveTransitive.ElementarySylowOrders

end CFSG

module

public import Mathlib.GroupTheory.OrderOfElement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CyclicPair.OddQuotient

universe u v

variable {E : Type u} {F : Type v} [Group E] [Group F]

theorem kernel_isMulCommutative (eta : E →* F)
    (hcentral : eta.ker ≤ Subgroup.center E) : IsMulCommutative eta.ker := by
  apply isMulCommutative_iff.mpr
  intro a b
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp (hcentral a.property) (b : E)).symm

theorem kernel_square_bijective (eta : E →* F) (hodd : Odd (Nat.card eta.ker)) :
    Function.Bijective (fun a : eta.ker => a ^ 2) := by
  exact hodd.coprime_two_right.pow_left_bijective

theorem kernel_unique_square_root (eta : E →* F) (hodd : Odd (Nat.card eta.ker))
    (c : eta.ker) : ∃! a : eta.ker, a ^ 2 = c := by
  obtain ⟨a, ha⟩ := (kernel_square_bijective eta hodd).surjective c
  exact ⟨a, ha, fun b hb => (kernel_square_bijective eta hodd).injective (hb.trans ha.symm)⟩

theorem kernel_square_one (eta : E →* F) (hodd : Odd (Nat.card eta.ker))
    {a : E} (ha : a ∈ eta.ker) (hsq : a ^ 2 = 1) : a = 1 := by
  let k : eta.ker := ⟨a, ha⟩
  have hk : k ^ 2 = (1 : eta.ker) ^ 2 := by
    apply Subtype.ext
    simpa using hsq
  exact congrArg Subtype.val ((kernel_square_bijective eta hodd).injective hk)

theorem map_involution (eta : E →* F) (hodd : Odd (Nat.card eta.ker))
    {x : E} (hx : orderOf x = 2) : orderOf (eta x) = 2 := by
  obtain ⟨hxsq, hxne⟩ := orderOf_eq_prime_iff.mp hx
  apply orderOf_eq_prime
  · rw [← map_pow, hxsq, map_one]
  · intro hxone
    exact hxne (kernel_square_one eta hodd (show x ∈ eta.ker from hxone) hxsq)

theorem exists_involution_lift (eta : E →* F) (hsurj : Function.Surjective eta)
    (hcentral : eta.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card eta.ker))
    {y : F} (hy : orderOf y = 2) : ∃ x : E, orderOf x = 2 ∧ eta x = y := by
  obtain ⟨a, ha⟩ := hsurj y
  obtain ⟨hysq, hyne⟩ := orderOf_eq_prime_iff.mp hy
  let c : eta.ker := ⟨(a ^ 2)⁻¹, by
    change eta ((a ^ 2)⁻¹) = 1
    rw [map_inv, map_pow, ha, hysq]
    simp⟩
  obtain ⟨k, hk⟩ := (kernel_square_bijective eta hodd).surjective c
  have hcomm : Commute a (k : E) :=
    Subgroup.mem_center_iff.mp (hcentral k.property) a
  have hksq : (k : E) ^ 2 = (a ^ 2)⁻¹ := congrArg Subtype.val hk
  have hsq : (a * (k : E)) ^ 2 = 1 := by
    rw [hcomm.mul_pow, hksq]
    exact mul_inv_cancel _
  have hmap : eta (a * (k : E)) = y := by
    rw [map_mul, ha, (show eta (k : E) = 1 from k.property), mul_one]
  refine ⟨a * (k : E), orderOf_eq_prime hsq ?_, hmap⟩
  intro hone
  have hyone : y = 1 := by rw [← hmap, hone, map_one]
  exact hyne hyone

theorem involution_lifts_injective (eta : E →* F)
    (hcentral : eta.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card eta.ker))
    {x w : E} (hx : orderOf x = 2) (hw : orderOf w = 2)
    (hmap : eta x = eta w) : x = w := by
  let c : E := x⁻¹ * w
  have hc : c ∈ eta.ker := by
    change eta (x⁻¹ * w) = 1
    rw [map_mul, map_inv, hmap]
    simp
  have hcomm : Commute x c := Subgroup.mem_center_iff.mp (hcentral hc) x
  have hprod : x * c = w := by simp [c]
  have hxsq : x ^ 2 = 1 := (orderOf_eq_prime_iff.mp hx).1
  have hwsq : w ^ 2 = 1 := (orderOf_eq_prime_iff.mp hw).1
  have hcsq : c ^ 2 = 1 := by
    calc
      c ^ 2 = x ^ 2 * c ^ 2 := by rw [hxsq, one_mul]
      _ = (x * c) ^ 2 := (hcomm.mul_pow 2).symm
      _ = w ^ 2 := congrArg (fun a : E => a ^ 2) hprod
      _ = 1 := hwsq
  have hcone : c = 1 := kernel_square_one eta hodd hc hcsq
  simpa [hcone] using hprod

theorem unique_involution_lift (eta : E →* F) (hsurj : Function.Surjective eta)
    (hcentral : eta.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card eta.ker))
    {y : F} (hy : orderOf y = 2) : ∃! x : E, orderOf x = 2 ∧ eta x = y := by
  obtain ⟨x, hx⟩ := exists_involution_lift eta hsurj hcentral hodd hy
  refine ⟨x, hx, ?_⟩
  intro w hw
  exact involution_lifts_injective eta hcentral hodd hw.1 hx.1 (hw.2.trans hx.2.symm)

end CFSG.ShultStronglyClosedTI.CyclicPair.OddQuotient

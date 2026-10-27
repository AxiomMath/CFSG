module

public import CFSG.Permutation.FiveTransitive.SevenInvolutionThreeSwaps
public import CFSG.Permutation.FiveTransitive.ThreeSwapMove

public section

namespace CFSG

namespace FiveTransitive.SevenCommutingSwapInvolution

open Equiv

theorem exists_conjugate {F : Type*} [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 7) (e : Fin 6 ↪ F)
    (x u : Perm F) (hx : x.IsSwap) (hu : u ^ 2 = 1) (hxu : Commute x u) :
    ∃ c : Perm F,
      c * x * c⁻¹ ∈ ThreeSwapTwoGroup.subgroup e ∧
      c * u * c⁻¹ ∈ ThreeSwapTwoGroup.subgroup e := by
  obtain ⟨a, b, hab, rfl⟩ := hx
  let t : Perm F := if u a = a then swap a b * u else u
  have ht2 : t ^ 2 = 1 := by
    dsimp [t]
    split
    · rw [hxu.mul_pow, hu]
      simp [pow_two]
    · exact hu
  have hta : t a = b := by
    dsimp [t]
    split
    · rename_i h
      simp only [Perm.mul_apply, h, swap_apply_left]
    · rename_i h
      exact (ThreeSwapMove.apply_eq_or_eq u a b hab hxu.symm).resolve_left h
  obtain ⟨c, hc⟩ := SevenInvolutionThreeSwaps.exists_conjugate hF e t ht2
  have hact : (c * t * c⁻¹) (c a) = c b := by
    simp [Perm.mul_apply, hta]
  have hxV : c * swap a b * c⁻¹ ∈ ThreeSwapTwoGroup.subgroup e := by
    rw [mul_swap_eq_swap_mul, mul_inv_cancel_right]
    rw [← hact]
    exact ThreeSwapMove.swap_image_mem e (c * t * c⁻¹) hc (c a)
  refine ⟨c, hxV, ?_⟩
  by_cases he : u a = a
  · have huExpr : u = swap a b * t := by
      simp only [t, if_pos he, swap_mul_self_mul]
    have hm := (ThreeSwapTwoGroup.subgroup e).mul_mem hxV hc
    change (MulAut.conj c (swap a b)) * (MulAut.conj c t) ∈ _ at hm
    rw [← map_mul, ← huExpr] at hm
    exact hm
  · simpa only [t, if_neg he] using hc

end FiveTransitive.SevenCommutingSwapInvolution

end CFSG

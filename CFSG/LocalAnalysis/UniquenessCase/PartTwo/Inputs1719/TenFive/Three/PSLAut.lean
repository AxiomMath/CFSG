module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

theorem ringEquiv_eq_one_of_card_three {K : Type*} [Field K] (hK : Nat.card K = 3)
    (σ : K ≃+* K) : σ = 1 := by
  classical
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by simpa using hK
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : CharP K 3 := charP_of_card_eq_prime hcard
  let f : ZMod 3 →+* K := ZMod.castHom (dvd_refl 3) K
  have hf : Function.Injective f := ZMod.castHom_injective (R := K)
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp [ZMod.card, hcard]⟩
  ext x
  obtain ⟨y, rfl⟩ := hfbij.2 x
  exact congrArg (fun g : ZMod 3 →+* K => g y) (RingHom.ext_zmod (σ.toRingHom.comp f) f)

theorem isGenGood_of_inv {S : Type*} [Group S] {σ : MulAut S} {y : S} {r : ℕ} (hr : r.Prime)
    (hy : orderOf y = r) (hσ : σ y = y⁻¹) (hd : 6 < dParam r) : IsGenGood σ := by
  have hr2 : r ≠ 2 := by
    intro hr'
    subst hr'
    have h0 : dParam 2 = 0 := by
      rw [dParam, show (2 : ZMod 2) = 0 from rfl, orderOf_eq_zero_iff']
      intro m hm
      rw [zero_pow hm.ne']
      exact zero_ne_one
    omega
  have hcop : (orderOf y).Coprime 2 := by
    rw [hy]
    exact (hr.odd_of_ne_two hr2).coprime_two_right
  refine ⟨1, fun _ => y, y⁻¹ * y⁻¹, r, hr, ?_, ?_, ?_⟩
  · have h : y⁻¹ * y⁻¹ = (y ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
    rw [h, orderOf_inv, hcop.orderOf_pow, hy]
  · exact Subgroup.subset_closure ⟨0, by simp [hσ]⟩
  · omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

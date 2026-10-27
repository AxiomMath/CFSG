module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bOffender

public section

namespace CFSG.Quasithin.G11.Harris.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section Conj

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

theorem dispRank_conj (a t : M ≃ₗ[ZMod 2] M) : dispRank (a * t * a⁻¹) = dispRank t := by
  unfold dispRank
  have h : (a * t * a⁻¹).toLinearMap - 1 =
      a.toLinearMap ∘ₗ (t.toLinearMap - 1) ∘ₗ a⁻¹.toLinearMap := by
    ext v
    simp
  have hr : LinearMap.range a⁻¹.toLinearMap = ⊤ := LinearEquiv.range a⁻¹
  rw [h, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ hr]
  exact LinearEquiv.finrank_map_eq a _

end Conj

variable {F : Type} [Field F] [CharP F 2] [Fintype F]

theorem rk_minorAut_pow_odd {f : ℕ} (hodd : Odd f) (z : antiSp F) :
    rk0 ((minorAut F ^ f) z) = rk1 z ∧ rk1 ((minorAut F ^ f) z) = rk0 z := by
  have h1 := rank_natRepS_parity z f
  have h2 := rank_natRepS_parity z (f + 1)
  rw [rank_natRepS_eq] at h1 h2
  have hf : f % 2 = 1 := Nat.odd_iff.mp hodd
  have hf1 : (f + 1) % 2 = 0 := by omega
  simp only [hf, hf1, one_ne_zero, ite_false, ite_true] at h1 h2
  refine ⟨h1, ?_⟩
  rw [← h2, rk1, pow_succ', MulAut.mul_apply, minorAut_apply]

section Outer

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] {π : antiSp F →* (M ≃ₗ[ZMod 2] M)}
  {A : Subgroup (M ≃ₗ[ZMod 2] M)}

theorem normAut_mem_inner_of_odd {f : ℕ} (hf : 2 ≤ f) (hodd : Odd f) (hK : Nat.card F = 2 ^ f)
    (H : Offender π A) {d j : ℕ} (hd : 1 ≤ d)
    (hdisp : ∀ z : antiSp F, z * z = 1 →
      dispRank (π z) = d * (if j % 2 = 0 then rk0 z else rk1 z)) (a : A) :
    normAut π H.inj A H.norm a ∈ inner (antiSp F) := by
  by_contra hout
  have hθθ : normAut π H.inj A H.norm a * normAut π H.inj A H.norm a = 1 := by
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (H.sq a.1 a.2)
    rw [this, map_one]
  obtain ⟨c, hc⟩ := outer_involution_conj hf hK _ hθθ hout
  set ρ := minorAut F with hρ
  set w : antiSp F := invX F with hw
  have hww : w * w = 1 := invX_mul_self
  set x : antiSp F := c * w * c⁻¹ with hx
  have hxx : x * x = 1 := by
    rw [hx]
    calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
      _ = 1 := by rw [hww]; group
  have hαx : normAut π H.inj A H.norm a x = c * (ρ ^ f) w * c⁻¹ := by
    have h1 : (MulAut.conj c)⁻¹ x = w := by rw [MulAut.conj_inv_apply, hx]; group
    rw [hc, MulAut.mul_apply, MulAut.mul_apply, h1, MulAut.conj_apply]
  set y : antiSp F := normAut π H.inj A H.norm a x with hy
  have hyy : y * y = 1 := by
    rw [hy, ← map_mul, hxx, map_one]
  have hπy : π y = a.1 * π x * a.1⁻¹ := π_normAut π H.inj A H.norm a x
  have hdy : dispRank (π y) = dispRank (π x) := by
    rw [hπy, dispRank_conj]
  have hrk := rk_minorAut_pow_odd hodd w
  have hy0 : rk0 y = 2 := by
    rw [hαx, (rk_conj c _).1, hrk.1, hw]; exact rk1_invX
  have hy1 : rk1 y = 1 := by
    rw [hαx, (rk_conj c _).2, hrk.2, hw]; exact rk0_invX
  have hx0 : rk0 x = 1 := by rw [hx, (rk_conj c _).1, hw]; exact rk0_invX
  have hx1 : rk1 x = 2 := by rw [hx, (rk_conj c _).2, hw]; exact rk1_invX
  have h := hdy
  rw [hdisp y hyy, hdisp x hxx, hy0, hy1, hx0, hx1] at h
  by_cases hj : j % 2 = 0
  · simp only [hj, ite_true] at h
    omega
  · simp only [hj, ite_false] at h
    omega

end Outer

end CFSG.Quasithin.G11.Harris.Sp4

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentPsuChain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentFpf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

private lemma k330c_three_ne_zero {F : Type*} [Field F] {ω : F} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) : (3 : F) ≠ 0 := by
  have hsum : (1 : F) + ω + ω ^ 2 = 0 := by
    have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by
      rw [show (ω - 1) * (1 + ω + ω ^ 2) = ω ^ 3 - 1 by ring, hω3, sub_self]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hω1)
  intro h30
  have hsq : (ω - 1) ^ 2 = 0 := by
    rw [show (ω - 1) ^ 2 = (1 + ω + ω ^ 2) - 3 * ω by ring, hsum, h30]
    ring
  exact hω1 (sub_eq_zero.mp (sq_eq_zero_iff.mp hsq))

private lemma k330c_eq_zero_of_mem_inf_ker {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] (g r : V ≃ₗ[F] V) (W : Submodule F V)
    (hW : W = LinearMap.ker ((r : V →ₗ[F] V) - 1))
    (hbot : LinearMap.ker ((g : V →ₗ[F] V) - 1) ⊓
      LinearMap.ker ((r : V →ₗ[F] V) - 1) = ⊥)
    {w : V} (hw : w ∈ W) (hgw : g w = w) : w = 0 := by
  have hker : w ∈ LinearMap.ker ((g : V →ₗ[F] V) - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact hgw
  have hmem : w ∈ LinearMap.ker ((g : V →ₗ[F] V) - 1) ⊓
      LinearMap.ker ((r : V →ₗ[F] V) - 1) := ⟨hker, by rw [← hW]; exact hw⟩
  rw [hbot] at hmem
  simpa using hmem

theorem psu_no_e9c7 {F : Type*} [Field F] [Finite F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hn : Module.finrank F V = 4 ∨ Module.finrank F V = 5)
    (hQ7 : ¬ 7 ∣ Nat.card F ∧ ¬ 7 ∣ Nat.card F - 1 ∧ ¬ 7 ∣ Nat.card F + 1)
    (ω : F) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (U : Subgroup (V ≃ₗ[F] V))
    (hdual : ∀ g ∈ U, g ^ 3 = 1 →
      Module.finrank F ↥(LinearMap.ker ((g : V →ₗ[F] V) - ω • 1)) =
        Module.finrank F ↥(LinearMap.ker ((g : V →ₗ[F] V) - ω ^ 2 • 1)))
    (x y r : V ≃ₗ[F] V) (hx : x ∈ U) (hy : y ∈ U) : ¬ E9C7Rel x y r := by
  classical
  rintro ⟨hx1, hy1, hxy1, hxy21, hx3, hy3, hr1, hr7, hxy, hxr, hyr⟩
  have h3 : (3 : F) ≠ 0 := k330c_three_ne_zero hω3 hω1
  have hcomm : Commute x y := hxy
  have hxyU : x * y ∈ U := U.mul_mem hx hy
  have hy2U : y ^ 2 ∈ U := U.pow_mem hy 2
  have hxy2U : x * y ^ 2 ∈ U := U.mul_mem hx hy2U
  have hxy3 : (x * y) ^ 3 = 1 := by rw [hcomm.mul_pow 3, hx3, hy3, one_mul]
  have hy6 : y ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hy3, one_pow]
  have hxy23 : (x * y ^ 2) ^ 3 = 1 := by
    rw [(hcomm.pow_right 2).mul_pow 3, hx3, one_mul, ← pow_mul,
      show (2 * 3 : ℕ) = 6 from rfl, hy6]
  have hxyr : (x * y) * r = r * (x * y) := by
    rw [mul_assoc, hyr, ← mul_assoc, hxr, mul_assoc]
  have hy2r : y ^ 2 * r = r * y ^ 2 := (show Commute y r from hyr).pow_left 2
  have hxy2r : (x * y ^ 2) * r = r * (x * y ^ 2) := by
    rw [mul_assoc, hy2r, ← mul_assoc, hxr, mul_assoc]
  have hxchain := psu_chain hn hQ7 ω hω3 hω1 hxr hx3 hx1 hr7 hr1 (hdual x hx hx3)
  have hychain := psu_chain hn hQ7 ω hω3 hω1 hyr hy3 hy1 hr7 hr1 (hdual y hy hy3)
  have hxychain :=
    psu_chain hn hQ7 ω hω3 hω1 hxyr hxy3 hxy1 hr7 hr1 (hdual (x * y) hxyU hxy3)
  have hxy2chain :=
    psu_chain hn hQ7 ω hω3 hω1 hxy2r hxy23 hxy21 hr7 hr1 (hdual (x * y ^ 2) hxy2U hxy23)
  set W : Submodule F V := LinearMap.ker ((r : V →ₗ[F] V) - 1) with hW
  have hWne : W ≠ ⊥ := by rw [hW]; exact hxchain.2.1
  have hWx : ∀ w ∈ W, x w ∈ W := by
    intro w hw
    rw [hW] at hw ⊢
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw ⊢
    have hcommx : (r : V →ₗ[F] V) (x w) = x ((r : V →ₗ[F] V) w) := by
      have h := congrArg (fun f : V ≃ₗ[F] V => f w) hxr
      simpa [LinearEquiv.mul_apply] using h.symm
    rw [hcommx, hw]
  have hWy : ∀ w ∈ W, y w ∈ W := by
    intro w hw
    rw [hW] at hw ⊢
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw ⊢
    have hcommy : (r : V →ₗ[F] V) (y w) = y ((r : V →ₗ[F] V) w) := by
      have h := congrArg (fun f : V ≃ₗ[F] V => f w) hyr
      simpa [LinearEquiv.mul_apply] using h.symm
    rw [hcommy, hw]
  have hfx1 : ∀ w ∈ W, x w = w → w = 0 :=
    fun w hw hxw => k330c_eq_zero_of_mem_inf_ker x r W hW hxchain.2.2 hw hxw
  have hfy1 : ∀ w ∈ W, y w = w → w = 0 :=
    fun w hw hyw => k330c_eq_zero_of_mem_inf_ker y r W hW hychain.2.2 hw hyw
  have hfxy1 : ∀ w ∈ W, (x * y) w = w → w = 0 :=
    fun w hw hxyw => k330c_eq_zero_of_mem_inf_ker (x * y) r W hW hxychain.2.2 hw hxyw
  have hfxy21 : ∀ w ∈ W, (x * y ^ 2) w = w → w = 0 :=
    fun w hw hxy2w => k330c_eq_zero_of_mem_inf_ker (x * y ^ 2) r W hW hxy2chain.2.2 hw hxy2w
  exact hWne (e9_fpf h3 x y hxy hx3 hy3 W hWx hWy hfx1 hfy1 hfxy1 hfxy21)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

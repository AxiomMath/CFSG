module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentPslChain
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentFpf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentDefs
import Mathlib.Algebra.CharP.CharAndCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

private lemma k330c_fix_free {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    {g r : V ≃ₗ[F] V}
    (h : LinearMap.ker ((g : V →ₗ[F] V) - 1) ⊓
      LinearMap.ker ((r : V →ₗ[F] V) - 1) = ⊥)
    {w : V} (hw : w ∈ LinearMap.ker ((r : V →ₗ[F] V) - 1)) (hgw : g w = w) : w = 0 := by
  have h1 : w ∈ LinearMap.ker ((g : V →ₗ[F] V) - 1) := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact hgw
  have h2 : w ∈ (⊥ : Submodule F V) := by
    rw [← h]
    exact ⟨h1, hw⟩
  simpa using h2

theorem psl_no_e9c7 {F : Type*} [Field F] [Finite F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hn : Module.finrank F V = 4 ∨ Module.finrank F V = 5)
    (hQ3 : Nat.card F % 3 = 2)
    (hQ7 : ¬ 7 ∣ Nat.card F ∧ ¬ 7 ∣ Nat.card F - 1 ∧ ¬ 7 ∣ Nat.card F + 1)
    (x y r : V ≃ₗ[F] V) : ¬ E9C7Rel x y r := by
  intro h
  obtain ⟨hx1, hy1, hxy_ne, hxy2_ne, hx3, hy3, hr1, hr7, hxyc, hxrc, hyrc⟩ := h
  have h3F : (3 : F) ≠ 0 := by
    intro h0
    have hdvd3 : ringChar F ∣ 3 := (ringChar.spec F 3).mp h0
    have hrc : ringChar F = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
      · exact absurd h1 (CharP.ringChar_ne_one (R := F))
      · exact h3
    haveI : Fintype F := Fintype.ofFinite F
    have hdvdF : 3 ∣ Fintype.card F :=
      (prime_dvd_char_iff_dvd_card (R := F) 3).mp (by rw [hrc])
    rw [← Nat.card_eq_fintype_card] at hdvdF
    rw [Nat.dvd_iff_mod_eq_zero] at hdvdF
    omega
  have hcxy : Commute x y := hxyc
  have hxrc' : Commute x r := hxrc
  have hyrc' : Commute y r := hyrc
  have hxy3 : (x * y) ^ 3 = 1 := by rw [hcxy.mul_pow 3, hx3, hy3, one_mul]
  have hy6 : y ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hy3, one_pow]
  have hxy23 : (x * y ^ 2) ^ 3 = 1 := by
    rw [(hcxy.pow_right 2).mul_pow 3, hx3, one_mul, ← pow_mul,
      show (2 * 3 : ℕ) = 6 from rfl, hy6]
  have hxyr : (x * y) * r = r * (x * y) := hxrc'.mul_left hyrc'
  have hxy2r : (x * y ^ 2) * r = r * (x * y ^ 2) := hxrc'.mul_left (hyrc'.pow_left 2)
  have hxchain := psl_chain hn hQ3 hQ7 (x := x) (r := r) hxrc hx3 hx1 hr7 hr1
  have hychain := psl_chain hn hQ3 hQ7 (x := y) (r := r) hyrc hy3 hy1 hr7 hr1
  have hxychain := psl_chain hn hQ3 hQ7 (x := x * y) (r := r) hxyr hxy3 hxy_ne hr7 hr1
  have hxy2chain := psl_chain hn hQ3 hQ7 (x := x * y ^ 2) (r := r) hxy2r hxy23 hxy2_ne hr7 hr1
  let W : Submodule F V := LinearMap.ker ((r : V →ₗ[F] V) - 1)
  have hWne : W ≠ ⊥ := hxchain.2.1
  have hWx : ∀ w ∈ W, x w ∈ W := by
    intro w hw
    change x w ∈ LinearMap.ker ((r : V →ₗ[F] V) - 1)
    have hxrL : Commute (x : V →ₗ[F] V) (r : V →ₗ[F] V) := by
      have hh := congrArg (fun f : V ≃ₗ[F] V => (f : V →ₗ[F] V)) hxrc
      have hh' : (x : V →ₗ[F] V) * (r : V →ₗ[F] V) =
          (r : V →ₗ[F] V) * (x : V →ₗ[F] V) := by
        simpa only [LinearEquiv.coe_toLinearMap_mul] using hh
      exact hh'
    have hw' : (r : V →ₗ[F] V) w = w := by
      have hh := LinearMap.mem_ker.mp hw
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hh
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    change (r : V →ₗ[F] V) ((x : V →ₗ[F] V) w) = (x : V →ₗ[F] V) w
    have hcomm : (r : V →ₗ[F] V) ((x : V →ₗ[F] V) w) =
        (x : V →ₗ[F] V) ((r : V →ₗ[F] V) w) := by
      have hh := congrArg (fun f : V →ₗ[F] V => f w) hxrL.symm.eq
      rwa [Module.End.mul_apply, Module.End.mul_apply] at hh
    rw [hcomm, hw']
  have hWy : ∀ w ∈ W, y w ∈ W := by
    intro w hw
    change y w ∈ LinearMap.ker ((r : V →ₗ[F] V) - 1)
    have hyrL : Commute (y : V →ₗ[F] V) (r : V →ₗ[F] V) := by
      have hh := congrArg (fun f : V ≃ₗ[F] V => (f : V →ₗ[F] V)) hyrc
      have hh' : (y : V →ₗ[F] V) * (r : V →ₗ[F] V) =
          (r : V →ₗ[F] V) * (y : V →ₗ[F] V) := by
        simpa only [LinearEquiv.coe_toLinearMap_mul] using hh
      exact hh'
    have hw' : (r : V →ₗ[F] V) w = w := by
      have hh := LinearMap.mem_ker.mp hw
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hh
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    change (r : V →ₗ[F] V) ((y : V →ₗ[F] V) w) = (y : V →ₗ[F] V) w
    have hcomm : (r : V →ₗ[F] V) ((y : V →ₗ[F] V) w) =
        (y : V →ₗ[F] V) ((r : V →ₗ[F] V) w) := by
      have hh := congrArg (fun f : V →ₗ[F] V => f w) hyrL.symm.eq
      rwa [Module.End.mul_apply, Module.End.mul_apply] at hh
    rw [hcomm, hw']
  have hx1' : ∀ w ∈ W, x w = w → w = 0 :=
    fun w hw hgw => k330c_fix_free hxchain.2.2 hw hgw
  have hy1' : ∀ w ∈ W, y w = w → w = 0 :=
    fun w hw hgw => k330c_fix_free hychain.2.2 hw hgw
  have hxy1' : ∀ w ∈ W, (x * y) w = w → w = 0 :=
    fun w hw hgw => k330c_fix_free hxychain.2.2 hw hgw
  have hxy2' : ∀ w ∈ W, (x * y ^ 2) w = w → w = 0 :=
    fun w hw hgw => k330c_fix_free hxy2chain.2.2 hw hgw
  exact hWne (e9_fpf h3F x y hxyc hx3 hy3 W hWx hWy hx1' hy1' hxy1' hxy2')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

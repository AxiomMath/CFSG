module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828UKl1
public import CFSG.Quasithin.Vol2.Ch8Sec2L828UF16

public section

namespace CFSG.Quasithin.H13

open CFSG.Open Polynomial

section Kl2

variable {K M : Type} [Group K] [AddCommGroup M] [Module (ZMod 2) M]

theorem ob5_K_linear [Module (GaloisField 2 4) M] (R : K →* AddMonoid.End M)
    (σ : AddMonoid.End M) (hσL : aeval (ob5L σ) (cyclotomic 5 (ZMod 2)) = 0)
    (hcomm : ∀ κ : K, R κ * σ = σ * R κ)
    (hF : ∀ (a : GaloisField 2 4) (m : M), a • m = ob5_f16Hom (ob5L σ) hσL a m) :
    ∃ φ : K →* (M →ₗ[GaloisField 2 4] M)ˣ, ∀ (κ : K) (m : M),
      ((φ κ : (M →ₗ[GaloisField 2 4] M)ˣ) : M →ₗ[GaloisField 2 4] M) m = R κ m := by
  have hlin : ∀ κ : K, ∀ (a : GaloisField 2 4) (m : M), R κ (a • m) = a • R κ m := by
    intro κ a m
    have hc : Commute (ob5L (R κ)) (ob5L σ) := by
      show ob5L (R κ) * ob5L σ = ob5L σ * ob5L (R κ)
      rw [← ob5L_mul, ← ob5L_mul, hcomm κ]
    have hc' := ob5_f16Hom_commute (ob5L σ) hσL (ob5L (R κ)) hc a
    have := congrArg (fun T : Module.End (ZMod 2) M => T m) hc'
    simp only [Module.End.mul_apply] at this
    rw [hF, hF]
    simp only [ob5L_apply] at this
    exact this
  let lin : K → (M →ₗ[GaloisField 2 4] M) := fun κ =>
    { toFun := R κ
      map_add' := fun x y => (R κ).map_add x y
      map_smul' := fun a m => hlin κ a m }
  have hlin_mul : ∀ κ κ' : K, lin (κ * κ') = lin κ * lin κ' := fun κ κ' =>
    LinearMap.ext fun m => by
      show R (κ * κ') m = R κ (R κ' m)
      rw [map_mul]
      rfl
  have hlin_one : lin 1 = 1 := LinearMap.ext fun m => by
    show R 1 m = m
    rw [map_one]
    rfl
  let φ0 : K → (M →ₗ[GaloisField 2 4] M)ˣ := fun κ =>
    ⟨lin κ, lin κ⁻¹, by rw [← hlin_mul, mul_inv_cancel, hlin_one],
      by rw [← hlin_mul, inv_mul_cancel, hlin_one]⟩
  exact ⟨{ toFun := φ0
           map_one' := Units.ext hlin_one
           map_mul' := fun κ κ' => Units.ext (hlin_mul κ κ') }, fun κ m => rfl⟩

end Kl2

end CFSG.Quasithin.H13

module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828UKl2
public import CFSG.Quasithin.Vol2.Ch8Sec2L828USL2Hom

public section

namespace CFSG.Quasithin.H13

open CFSG.Open Polynomial
open scoped IsMulCommutative
open CFSG.Quasithin.H13.L828T
open CFSG.Quasithin.H

theorem ob5L_pow' {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (f : AddMonoid.End M) (n : ℕ) :
    ob5L (f ^ n) = (ob5L f) ^ n := by
  induction n with
  | zero =>
    ext m
    rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, ob5L_mul, ih]

theorem ob5_rep_of_module {K M : Type} [Group K] [Group.IsPerfect K] [AddCommGroup M]
    [Module (ZMod 2) M] [Module (GaloisField 2 4) M] [Module.Finite (GaloisField 2 4) M]
    (σ : AddMonoid.End M) (hσL : aeval (ob5L σ) (cyclotomic 5 (ZMod 2)) = 0)
    (hF : ∀ (a : GaloisField 2 4) (m : M), a • m = ob5_f16Hom (ob5L σ) hσL a m)
    (hfin : Module.finrank (GaloisField 2 4) M = 2)
    (R : K →* AddMonoid.End M) (hcomm : ∀ κ : K, R κ * σ = σ * R κ) :
    ∃ (φ : K →* (M →ₗ[GaloisField 2 4] M)ˣ)
      (θ : K →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)),
      (∀ κ : K, ((θ κ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 4)) =
          ob5mat (Module.finBasisOfFinrankEq (GaloisField 2 4) M hfin) (φ κ)) ∧
      (∀ (κ : K) (m : M), ((φ κ : (M →ₗ[GaloisField 2 4] M)ˣ) : M →ₗ[GaloisField 2 4] M) m =
        R κ m) := by
  obtain ⟨φ, hφ⟩ := ob5_K_linear R σ hσL hcomm hF
  obtain ⟨θ, hθ⟩ := ob5_sl_hom (Module.finBasisOfFinrankEq (GaloisField 2 4) M hfin) φ
  exact ⟨φ, θ, hθ, hφ⟩

end CFSG.Quasithin.H13

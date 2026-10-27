module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.Quasithin.D35Core

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_fix_involution [CharP K 2] (hV : Module.finrank K V = 3) {g : V ≃ₗ[K] V}
    (hg2 : ∀ v, g (g v) = v) (hg1 : g ≠ 1) :
    Module.finrank K (LinearMap.ker ((g : V →ₗ[K] V) - LinearMap.id)) = 2 := by
  set T : V →ₗ[K] V := (g : V →ₗ[K] V) - LinearMap.id with hT
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hTT : ∀ v, T (T v) = 0 := fun v => by
    have : T (T v) = (2 : K) • (v - g v) := by
      simp only [hT, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub, hg2]
      module
    rw [this, h2, zero_smul]
  have hle : LinearMap.range T ≤ LinearMap.ker T := by
    rintro _ ⟨v, rfl⟩
    exact hTT v
  have hT0 : T ≠ 0 := fun h => hg1 (LinearEquiv.ext fun v => by
    have := LinearMap.congr_fun h v
    simpa [hT, sub_eq_zero] using this)
  have hr : LinearMap.range T ≠ ⊥ := fun h => hT0 (LinearMap.range_eq_bot.1 h)
  have hr1 : Module.finrank K (LinearMap.range T) ≠ 0 := fun h => hr (Submodule.finrank_eq_zero.1 h)
  have hrk := LinearMap.finrank_range_add_finrank_ker T
  have hmono := Submodule.finrank_mono hle
  omega

theorem card_fix_involution [CharP K 2] (hV : Module.finrank K V = 3) {g : V ≃ₗ[K] V}
    (hg2 : ∀ v, g (g v) = v) (hg1 : g ≠ 1) : Nat.card {w : V // g w = w} = Nat.card K ^ 2 := by
  have e : {w : V // g w = w} ≃ LinearMap.ker ((g : V →ₗ[K] V) - LinearMap.id) :=
    Equiv.subtypeEquivRight fun w => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      rfl
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K), finrank_fix_involution hV hg2 hg1]

end CFSG.Quasithin.D35Core

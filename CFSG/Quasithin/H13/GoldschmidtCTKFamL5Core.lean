module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import CFSG.Quasithin.H13.GoldschmidtCTKFamL5Fix
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.Quasithin.H13.CTK.L5

open scoped Pointwise

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
variable {Γ : Type} [Group Γ] (act : Γ →* (W ≃ₗ[K] W))

@[expose] def Tset (F : Submodule K W) : Set Γ :=
  {g | (∀ f ∈ F, act g f = f) ∧ ∀ w, act g w - w ∈ F}

@[expose] def dmap (F : Submodule K W) (g : Γ) (hg : g ∈ Tset act F) : (W ⧸ F) →ₗ[K] F :=
  F.liftQ (((act g).toLinearMap - LinearMap.id).codRestrict F (fun w => hg.2 w)) (by
    intro f hf
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    simp [hg.1 f hf])

theorem dmap_injective [Finite W] (hact : Function.Injective act) (F : Submodule K W) :
    ∀ (g g' : Γ) (hg : g ∈ Tset act F) (hg' : g' ∈ Tset act F),
      dmap act F g hg = dmap act F g' hg' → g = g' := by
  intro g g' hg hg' h
  apply hact
  ext w
  have := congrArg (fun φ : (W ⧸ F) →ₗ[K] F => (φ (Submodule.Quotient.mk w) : W)) h
  simpa [dmap, sub_left_inj] using this

theorem card_hom_quot [Finite W] (hK : Nat.card K = 2) (hdim : Module.finrank K W = 5)
    (U : Submodule K W) (hU : Nat.card U = 2 ∨ Nat.card U = 16) :
    Nat.card ((W ⧸ U) →ₗ[K] U) = 16 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have : Fintype U := Fintype.ofFinite U
  have hUc : Fintype.card U = 2 ^ Module.finrank K U := by
    rw [Module.card_eq_pow_finrank (K := K) (V := U), ← Nat.card_eq_fintype_card, hK]
  have hUc' : Nat.card U = 2 ^ Module.finrank K U := by rw [Nat.card_eq_fintype_card, hUc]
  have hsum := Submodule.finrank_quotient_add_finrank U
  have hf : Module.finrank K U = 1 ∨ Module.finrank K U = 4 := by
    rcases hU with h | h
    · left
      have h2 : 2 ^ Module.finrank K U = 2 ^ 1 := by rw [← hUc', h]; norm_num
      exact Nat.pow_right_injective (le_refl 2) h2
    · right
      have h2 : 2 ^ Module.finrank K U = 2 ^ 4 := by rw [← hUc', h]; norm_num
      exact Nat.pow_right_injective (le_refl 2) h2
  have hfin : Module.finrank K ((W ⧸ U) →ₗ[K] U) = 4 := by
    rw [Module.finrank_linearMap K K]
    rcases hf with h | h <;> rw [h] <;> omega
  have : Finite ((W ⧸ U) →ₗ[K] U) := Module.finite_of_finite K
  have : Fintype ((W ⧸ U) →ₗ[K] U) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K), ← Nat.card_eq_fintype_card,
    hK, hfin]
  norm_num

theorem tset_ncard_le [Finite W] (hK : Nat.card K = 2) (hdim : Module.finrank K W = 5)
    (hact : Function.Injective act) (F : Submodule K W)
    (hF : Nat.card F = 2 ∨ Nat.card F = 16) : (Tset act F).ncard ≤ 16 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Finite ((W ⧸ F) →ₗ[K] F) := Module.finite_of_finite K
  have hHom := card_hom_quot hK hdim F hF
  let ι : ↥(Tset act F) → ((W ⧸ F) →ₗ[K] F) := fun g => dmap act F g g.2
  have hι : Function.Injective ι := fun a b h =>
    Subtype.ext (dmap_injective act hact F a b a.2 b.2 h)
  have := Nat.card_le_card_of_injective ι hι
  rw [Nat.card_coe_set_eq, hHom] at this
  exact this

theorem act_apply_inv (g : Γ) (w : W) : act g (act g⁻¹ w) = w := by
  rw [← LinearEquiv.mul_apply, ← map_mul]
  simp

@[expose] def stabF (F : Submodule K W) : Subgroup Γ where
  carrier := {h | ∀ w, w ∈ F ↔ act h w ∈ F}
  mul_mem' := fun {a b} (ha : ∀ w, w ∈ F ↔ act a w ∈ F) (hb : ∀ w, w ∈ F ↔ act b w ∈ F) w => by
    rw [map_mul, LinearEquiv.mul_apply, hb w, ← ha (act b w)]
  one_mem' := fun w => by simp
  inv_mem' := fun {a} (ha : ∀ w, w ∈ F ↔ act a w ∈ F) w => by
    have := ha (act a⁻¹ w)
    rw [act_apply_inv] at this
    exact this.symm

theorem conj_mem_Tset (F : Submodule K W) {h : Γ} (hh : h ∈ stabF act F) {g : Γ}
    (hg : g ∈ Tset act F) : h * g * h⁻¹ ∈ Tset act F := by
  have hh' : h⁻¹ ∈ stabF act F := (stabF act F).inv_mem hh
  refine ⟨fun f hf => ?_, fun w => ?_⟩
  · have h1 : act h⁻¹ f ∈ F := (hh' f).1 hf
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg.1 _ h1,
      act_apply_inv]
  · have h1 := (hh (act g (act h⁻¹ w) - act h⁻¹ w)).1 (hg.2 (act h⁻¹ w))
    have h2 : act (h * g * h⁻¹) w - w = act h (act g (act h⁻¹ w) - act h⁻¹ w) := by
      rw [map_sub, act_apply_inv, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [h2]
    exact h1

theorem stab_le_normalizer (V : Subgroup Γ) (F : Submodule K W)
    (hVT : (V : Set Γ) = Tset act F) : stabF act F ≤ Subgroup.normalizer (V : Set Γ) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hmem : ∀ k, k ∈ V ↔ k ∈ Tset act F := fun k => by
    rw [← hVT]
    rfl
  rw [hmem, hmem]
  constructor
  · exact conj_mem_Tset act F hh
  · intro hg
    have := conj_mem_Tset act F ((stabF act F).inv_mem hh) hg
    simpa [mul_assoc] using this

end CFSG.Quasithin.H13.CTK.L5

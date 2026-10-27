module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Quasithin.SteinbergBSOddPlaneSylow
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.ABGLocalTools
open scoped IsMulCommutative Pointwise

theorem perfect_sylow_two_irreducible_of_finrank_eq_two
    {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) {L : Type*} [Group L] [Finite L] [Group.IsPerfect L] {W : Type*}
    [CommGroup W] [instM : Module (ZMod p) (Additive W)]
    (hfin : Module.finrank (ZMod p) (Additive W) = 2) (β : L →* MulAut W) (hβ : β ≠ 1)
    (S : Sylow 2 L) (M : Subgroup W) (hM : ∀ s ∈ (S : Subgroup L), ∀ w ∈ M, β s w ∈ M) :
    M = ⊥ ∨ M = ⊤ := by
  classical
  let e : MulAut W → (Additive W ≃ₗ[ZMod p] Additive W) := fun σ =>
    LinearEquiv.ofLinearMap ((MulEquiv.toAdditive σ : Additive W ≃+ Additive W).toAddMonoidHom
      |>.toZModLinearMap p)
      ((MulEquiv.toAdditive σ.symm : Additive W ≃+ Additive W).toAddMonoidHom.toZModLinearMap p)
      (by ext w; exact congrArg Additive.ofMul (σ.apply_symm_apply w.toMul))
      (by ext w; exact congrArg Additive.ofMul (σ.symm_apply_apply w.toMul))
  have he : ∀ σ (w : W), e σ (Additive.ofMul w) = Additive.ofMul (σ w) := fun _ _ => rfl
  let α : L →* (Additive W ≃ₗ[ZMod p] Additive W) :=
    { toFun := fun l => e (β l)
      map_one' := by
        refine LinearEquiv.ext fun w => ?_
        change e (β 1) (Additive.ofMul w.toMul) = Additive.ofMul w.toMul
        rw [he, map_one]
        rfl
      map_mul' := fun a b => by
        refine LinearEquiv.ext fun w => ?_
        change e (β (a * b)) (Additive.ofMul w.toMul) =
          e (β a) (e (β b) (Additive.ofMul w.toMul))
        rw [he, he, he, map_mul]
        rfl }
  have hα : α ≠ 1 := by
    intro h
    apply hβ
    ext l w
    have h1 := congrArg (fun f : Additive W ≃ₗ[ZMod p] Additive W => f (Additive.ofMul w))
      (DFunLike.congr_fun h l)
    exact congrArg Additive.toMul h1
  have h := SteinbergBS.nq_perfect_odd_plane_sylow_two_irreducibility hp5 hfin α hα S
    (AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup M)) fun s hs w hw =>
      hM s hs w.toMul hw
  rcases h with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : Additive.ofMul w ∈ AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup M) := hw
    rw [h, Submodule.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (congrArg Additive.toMul h1)
  · right
    rw [eq_top_iff]
    intro w _
    have h1 : Additive.ofMul w ∈ AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup M) := by
      rw [h]
      exact Submodule.mem_top
    exact h1

theorem perfect_sylow_two_irreducible_of_card_eq_sq
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L] {W : Type*} [Group W]
    [IsMulCommutative W] (hWp : ∀ w : W, w ^ p = 1) (hcard : Nat.card W = p ^ 2)
    (β : L →* MulAut W) (hβ : β ≠ 1) (S : Sylow 2 L) (M : Subgroup W)
    (hM : ∀ s ∈ (S : Subgroup L), ∀ w ∈ M, β s w ∈ M) : M = ⊥ ∨ M = ⊤ := by
  have : Finite W := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.out.ne_zero)
  let inst : Module (ZMod p) (Additive W) := AddCommGroup.zmodModule fun x => by
    change Additive.ofMul (x.toMul ^ p) = 0
    rw [hWp]
    rfl
  have hfinite : Module.Finite (ZMod p) (Additive W) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod p) (Additive W) = 2 := by
    have h := @Module.natCard_eq_pow_finrank (ZMod p) (Additive W) _ _ inst hfinite
    rw [Nat.card_zmod, show Nat.card (Additive W) = Nat.card W from rfl, hcard] at h
    exact (Nat.pow_right_injective hp.out.two_le h).symm
  exact perfect_sylow_two_irreducible_of_finrank_eq_two (instM := inst) hp5 hfin β hβ S M hM

end CFSG.Quasithin.SteinbergCD

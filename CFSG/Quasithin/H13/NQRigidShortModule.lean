module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftAlt

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.SL2Modules (repOfSubgroup)

theorem exists_moduleEquiv {W₀ : Type} [CommGroup W₀] [Finite W₀] [Nontrivial W₀]
    (hW₀ : ∀ w : W₀, w * w = 1) {L₁ B₁ : Subgroup (MulAut W₀)}
    (hirr : ∀ U : Subgroup W₀, (∀ g ∈ L₁, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hBe : IsElemAbelian2 B₁) (hquad : IsQuadratic B₁)
    (hoff : Nat.card W₀ ≤ Nat.card B₁ * Nat.card (fixV B₁)) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W) (_ : Nontrivial W)
      (Ψ : MulAut W₀ ≃* (Module.End (ZMod 2) W)ˣ),
      (repOfSubgroup (L₁.map Ψ.toMonoidHom)).IsIrreducible ∧
        CFSG.IsElementaryAbelian 2 (B₁.map Ψ.toMonoidHom) ∧
        (∀ a ∈ B₁.map Ψ.toMonoidHom, ∀ b ∈ B₁.map Ψ.toMonoidHom, ∀ w : W,
          b.val (a.val w - w) = a.val w - w) ∧
        Nat.card W ≤ Nat.card (B₁.map Ψ.toMonoidHom) *
          Nat.card {w : W // ∀ a ∈ B₁.map Ψ.toMonoidHom, a.val w = w} := by
  classical
  obtain ⟨W, _, _, _, ⟨θ⟩⟩ := CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary hW₀
  set Ψ : MulAut W₀ ≃* (Module.End (ZMod 2) W)ˣ :=
    (CFSG.QuasithinUnique.Setup.Layer.binPsi θ).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).symm with hΨdef
  have hΨ : ∀ (φ : MulAut W₀) (w : W),
      (Ψ φ).val w = Multiplicative.toAdd (θ (φ (θ.symm (Multiplicative.ofAdd w)))) :=
    fun _ _ => rfl
  set c : W₀ → W := fun x => Multiplicative.toAdd (θ x) with hc
  have hc_symm : ∀ w : W, c (θ.symm (Multiplicative.ofAdd w)) = w := fun w => by
    simp [hc]
  have hc_mul : ∀ x y : W₀, c (x * y) = c x + c y := fun x y => by
    simp [hc]
  have hc_inv : ∀ x : W₀, c x⁻¹ = - c x := fun x => by
    simp [hc]
  have hc_inj : Function.Injective c := fun x y h => θ.injective (Multiplicative.toAdd.injective h)
  have hc_one : ∀ x : W₀, c x = 0 ↔ x = 1 := fun x => by
    constructor
    · intro h
      apply hc_inj
      rw [h]
      simp [hc]
    · rintro rfl
      simp [hc]
  have hΨc : ∀ (φ : MulAut W₀) (x : W₀), (Ψ φ).val (c x) = c (φ x) := fun φ x => by
    rw [hΨ]
    simp [hc]
  have hWnt : Nontrivial W := by
    obtain ⟨x, hx⟩ := exists_ne (1 : W₀)
    exact ⟨⟨c x, 0, fun h => hx ((hc_one x).mp h)⟩⟩
  refine ⟨W, inferInstance, inferInstance, inferInstance, hWnt, Ψ, ?_, ?_, ?_, ?_⟩
  · rw [CFSG.QuasithinUnique.Setup.Lift.isIrreducible_iff_invariant]
    refine ⟨hWnt, fun U hU => ?_⟩
    set U₀ : Subgroup W₀ :=
      { carrier := {x | c x ∈ U}
        one_mem' := by
          show c 1 ∈ U
          rw [(hc_one 1).mpr rfl]
          exact U.zero_mem
        mul_mem' := fun {x y} hx hy => by
          show c (x * y) ∈ U
          rw [hc_mul]
          exact U.add_mem hx hy
        inv_mem' := fun {x} hx => by
          show c x⁻¹ ∈ U
          rw [hc_inv]
          exact U.neg_mem hx } with hU₀
    have hU₀inv : ∀ g ∈ L₁, ∀ u ∈ U₀, g u ∈ U₀ := by
      intro g hg u hu
      have h1 := hU ⟨Ψ g, ⟨g, hg, rfl⟩⟩ (c u) hu
      show c (g u) ∈ U
      rw [← hΨc]
      exact h1
    rcases hirr U₀ hU₀inv with h0 | h0
    · left
      rw [eq_bot_iff]
      intro w hw
      have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by
        show c _ ∈ U
        rw [hc_symm]
        exact hw
      rw [h0, mem_bot] at hx
      rw [Submodule.mem_bot, ← hc_symm w, hx]
      exact (hc_one 1).mpr rfl
    · right
      rw [eq_top_iff]
      intro w _
      have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by rw [h0]; exact mem_top _
      have hx' : c (θ.symm (Multiplicative.ofAdd w)) ∈ U := hx
      rwa [hc_symm] at hx'
  · have hE : CFSG.IsElementaryAbelian 2 ↥B₁ :=
      { is_comm := ⟨fun a b => Subtype.ext (hBe.1 a a.2 b b.2)⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
          Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hBe.2 a a.2) }
    exact CFSG.QuasithinUnique.Setup.Layer.isElementaryAbelian_map Ψ.toMonoidHom B₁
  · rintro _ ⟨a₀, ha₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩ w
    set x := θ.symm (Multiplicative.ofAdd w) with hx
    have hw : w = c x := (hc_symm w).symm
    have hy : a₀ x * x⁻¹ ∈ fixV B₁ := hquad (subset_closure ⟨a₀, ha₀, x, rfl⟩)
    have h1 : (Ψ a₀).val w - w = c (a₀ x * x⁻¹) := by
      rw [hw, hΨc, hc_mul, hc_inv, sub_eq_add_neg]
    rw [MulEquiv.coe_toMonoidHom, h1, hΨc, hy b₀ hb₀]
  · have hcard1 : Nat.card W = Nat.card W₀ :=
      (Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)).symm
    have hcard2 : Nat.card ↥(B₁.map Ψ.toMonoidHom) = Nat.card ↥B₁ :=
      card_map_of_injective (f := Ψ.toMonoidHom) Ψ.injective
    have hcard3 : Nat.card {w : W // ∀ b ∈ B₁.map Ψ.toMonoidHom, b.val w = w} =
        Nat.card ↥(fixV B₁) := by
      symm
      refine Nat.card_congr
        { toFun := fun v => ⟨c v, ?_⟩
          invFun := fun w => ⟨θ.symm (Multiplicative.ofAdd w.1), ?_⟩
          left_inv := fun v => Subtype.ext (by simp [hc])
          right_inv := fun w => Subtype.ext (hc_symm w.1) }
      · rintro _ ⟨b, hb, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, hΨc, v.2 b hb]
      · intro b hb
        have h1 := w.2 (Ψ b) ⟨b, hb, rfl⟩
        apply hc_inj
        rw [← hΨc, hc_symm]
        exact h1
    rw [hcard1, hcard2, hcard3]
    exact hoff

end CFSG.Quasithin.H13.NQRigid

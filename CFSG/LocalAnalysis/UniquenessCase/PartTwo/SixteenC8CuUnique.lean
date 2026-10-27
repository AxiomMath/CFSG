module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuClassify
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.Quasithin.SmithCurtis CFSG.QuasithinUnique.Setup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

theorem cu_nonempty_equiv_of_isSpn {X : Type} [Group X] (h : IsSpn X 6 1) :
    Nonempty (G6 ≃* X) := by
  obtain ⟨e⟩ := c8_nonempty_mulEquiv_of_isSpn h
  obtain ⟨f⟩ := nonempty_g6_mulEquiv
  exact ⟨f.trans e.symm⟩

theorem cu_card_of_rk {W : Type} [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    (hrk : rk ↥(⊤ : Subgroup W) = 8) : Nat.card W = 2 ^ 8 := by
  have hP : IsPGroup 2 W := fun w => ⟨1, by simpa using hexp w⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have h : rk ↥(⊤ : Subgroup W) = n := by
    unfold rk
    rw [Subgroup.card_top, hn]
    exact padicValNat.prime_pow n
  rw [hn, ← hrk, h]

theorem cu_binModel {W : Type} [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (hirr : IsIrrOn L ⊤ ⊥) {S : Type} [Group S] (e : S ≃* ↥L) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Finite V)
      (ρ : Representation (ZMod 2) S V) (θ : W ≃* Multiplicative V),
      IsSimpleRep ρ ∧ ∀ (s : S) (w : W),
        θ ((e s : MulAut W) w) = Multiplicative.ofAdd (ρ s (Multiplicative.toAdd (θ w))) := by
  classical
  have hW : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hexp w
  obtain ⟨V, _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary hW
  set Ψ : MulAut W ≃* (Module.End (ZMod 2) V)ˣ :=
    (Layer.binPsi θ).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm
    with hΨdef
  have hΨ : ∀ (φ : MulAut W) (w : V),
      (Ψ φ).val w = Multiplicative.toAdd (θ (φ (θ.symm (Multiplicative.ofAdd w)))) :=
    fun _ _ => rfl
  set c : W → V := fun x => Multiplicative.toAdd (θ x) with hc
  have hc_symm : ∀ w : V, c (θ.symm (Multiplicative.ofAdd w)) = w := fun w => by simp [hc]
  have hc_mul : ∀ x y : W, c (x * y) = c x + c y := fun x y => by simp [hc]
  have hc_inv : ∀ x : W, c x⁻¹ = - c x := fun x => by simp [hc]
  have hc_inj : Function.Injective c := fun x y h => θ.injective (Multiplicative.toAdd.injective h)
  have hc_one : ∀ x : W, c x = 0 ↔ x = 1 := fun x => by
    constructor
    · intro h
      apply hc_inj
      rw [h]
      simp [hc]
    · rintro rfl
      simp [hc]
  have hΨc : ∀ (φ : MulAut W) (x : W), (Ψ φ).val (c x) = c (φ x) := fun φ x => by
    rw [hΨ]
    simp [hc]
  have hWnt : Nontrivial V := by
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt hirr.1
    exact ⟨⟨c x, 0, fun h => hx ((Subgroup.mem_bot).mpr ((hc_one x).mp h))⟩⟩
  have hFin : Finite V := inferInstance
  let ρ : Representation (ZMod 2) S V :=
    (Units.coeHom (Module.End (ZMod 2) V)).comp (Ψ.toMonoidHom.comp (L.subtype.comp e.toMonoidHom))
  have hρ : ∀ (s : S) (v : V), ρ s v = (Ψ (e s : MulAut W)).val v := fun _ _ => rfl
  refine ⟨V, inferInstance, inferInstance, hFin, ρ, θ, ⟨hWnt, fun U hU => ?_⟩, ?_⟩
  · set U₀ : Subgroup W :=
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
    have hU₀inv : StableUnder L U₀ := by
      intro g hg u hu
      have h1 := hU (e.symm ⟨g, hg⟩) (c u) hu
      rw [hρ, MulEquiv.apply_symm_apply] at h1
      show c (g u) ∈ U
      rw [← hΨc]
      exact h1
    rcases hirr.2.2.2 U₀ hU₀inv bot_le le_top with h0 | h0
    · left
      rw [eq_bot_iff]
      intro w hw
      have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by
        show c _ ∈ U
        rw [hc_symm]
        exact hw
      rw [h0, Subgroup.mem_bot] at hx
      rw [Submodule.mem_bot, ← hc_symm w, hx]
      exact (hc_one 1).mpr rfl
    · right
      rw [eq_top_iff]
      intro w _
      have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by rw [h0]; exact Subgroup.mem_top _
      have hx' : c (θ.symm (Multiplicative.ofAdd w)) ∈ U := hx
      rwa [hc_symm] at hx'
  · intro s w
    rw [hρ, hΨc]
    simp [hc]

theorem cu_finrank_eq {W : Type} [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ 2 = 1)
    (hrk : rk ↥(⊤ : Subgroup W) = 8) {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (θ : W ≃* Multiplicative V) : Module.finrank (ZMod 2) V = 8 := by
  have h1 : Nat.card V = 2 ^ 8 := by
    rw [← cu_card_of_rk hexp hrk]
    exact (Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)).symm
  have h2 : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact Nat.pow_right_injective (le_refl 2) (h2.symm.trans h1)

theorem rSp6SpinUnique_holds : RSp6SpinUnique := by
  intro W₁ W₂ _ _ _ _ hexp₁ hexp₂ H₁ H₂ hS₁ hS₂ hrk₁ hrk₂ hirr₁ hirr₂
  obtain ⟨e₁⟩ := cu_nonempty_equiv_of_isSpn hS₁
  obtain ⟨e₂⟩ := cu_nonempty_equiv_of_isSpn hS₂
  obtain ⟨V₁, _, _, _, ρ₁, θ₁, hs₁, hθ₁⟩ := cu_binModel hexp₁ hirr₁ e₁
  obtain ⟨V₂, _, _, _, ρ₂, θ₂, hs₂, hθ₂⟩ := cu_binModel hexp₂ hirr₂ e₂
  obtain ⟨β, hβ⟩ := classify_eight hs₁ hs₂ (cu_finrank_eq hexp₁ hrk₁ θ₁)
    (cu_finrank_eq hexp₂ hrk₂ θ₂)
  refine ⟨e₁.symm.trans e₂, θ₁.trans ((AddEquiv.toMultiplicative β.toAddEquiv).trans θ₂.symm), ?_⟩
  intro h w
  obtain ⟨g, rfl⟩ := e₁.surjective h
  apply θ₂.injective
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  rw [hθ₂, hθ₁]
  simp [hβ]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

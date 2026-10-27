module

public import CFSG.Quasithin.Background.SmithB45J2Holds

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.J2Mod

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.B45Mat CFSG.Quasithin.J2Row
  CFSG.Quasithin.J2Model FieldFour Matrix Module

section Binary


theorem j2_binary_small_28 (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (τ : Representation (ZMod 2) G6 W) (hτ : τ.IsIrreducible)
    (hW : finrank (ZMod 2) W < 28) :
    Nonempty (τ.Equiv (matrixBaseChange (RingHom.id (ZMod 2)) rep1)) ∨
      Nonempty (τ.Equiv (restrictF4 rep6a)) := by
  refine binary_coords_elim W τ hτ fun N hN hτN U hU0 hUirr => ?_
  obtain ⟨eτ⟩ := hτN
  let k := AlgebraicClosure (ZMod 2)
  obtain ⟨-, i, ⟨e⟩⟩ := j2ClosureRep_complete k U.toSubmodule U.toRepresentation hUirr
  have hdimU : finrank k U.toSubmodule = j2Dim i := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  have hUle : finrank k U.toSubmodule ≤ finrank (ZMod 2) W := by
    have h1 := Submodule.finrank_le U.toSubmodule
    rwa [Module.finrank_fin_fun] at h1
  fin_cases i
  ·
    obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_binary rep1 N (isIrreducible_rep1 _) hN _ _
      (incl_comp_ne_zero U hU0 e)
    exact Or.inl ⟨eτ.trans e'⟩
  ·
    change U.toRepresentation.Equiv (matrixBaseChange (toField k) rep6a) at e
    have hd := two_mul_le_of_frob _ U hUirr (toField k) e
      (isEmpty_equiv_of_trace k rep6a rep6b w6 trace_ne_6)
    obtain ⟨e'⟩ := nonempty_equiv_restrictF4 N hN (by omega) (toField k) _ (fun _ => rfl) _
      (incl_comp_ne_zero U hU0 e)
    exact Or.inr ⟨eτ.trans e'⟩
  ·
    change U.toRepresentation.Equiv (matrixBaseChange (toField k) rep6b) at e
    have hd := two_mul_le_of_frob _ U hUirr (toField k) e
      (isEmpty_equiv_of_trace k rep6b (twist rep6b) w6 (by
        have h1 : Matrix.trace (rep6b w6) = ω₂ := by rw [trace_twist, trace_rep6a_w6, frob_ω]
        rw [trace_twist rep6b, h1, frob_ω₂]
        exact ω_ne_ω₂.symm))
    have e₁ : U.toRepresentation.Equiv (matrixBaseChange ((toField k).comp frob) rep6a) :=
      e.trans (Representation.Equiv.mk (LinearEquiv.refl _ _) fun g =>
        by rw [rep6b, matrixBaseChange_twist]; rfl)
    obtain ⟨e'⟩ := nonempty_equiv_restrictF4 N hN (by omega) ((toField k).comp frob) _
      (fun x => by rw [RingHom.comp_apply, RingHom.comp_apply, frob_ofPrime]) _
      (incl_comp_ne_zero U hU0 e₁)
    exact Or.inr ⟨eτ.trans e'⟩
  ·
    change U.toRepresentation.Equiv (matrixBaseChange (toField k) rep14a) at e
    have hd := two_mul_le_of_frob _ U hUirr (toField k) e
      (isEmpty_equiv_of_trace k rep14a rep14b w14 trace_ne_14)
    omega
  ·
    change U.toRepresentation.Equiv (matrixBaseChange (toField k) rep14b) at e
    have hd := two_mul_le_of_frob _ U hUirr (toField k) e
      (isEmpty_equiv_of_trace k rep14b (twist rep14b) w14 (by
        have h1 : Matrix.trace (rep14b w14) = ω := by
          rw [trace_twist, trace_rep14a_w14, frob_ω₂]
        rw [trace_twist rep14b, h1, frob_ω]
        exact ω_ne_ω₂))
    omega
  all_goals
    exfalso
    simp only [j2Dim] at hdimU
    norm_num [hdimU] at hUle
    omega

end Binary

theorem finrank_lt_of_card_lt_28 {W : Type} [CommGroup W] (hV : ∀ w : W, w ^ 2 = 1)
    [Finite W] (hcard : Nat.card W < 2 ^ 28) :
    finrank (ZMod 2) (F2Vec W hV) < 28 := by
  have h1 : Nat.card (F2Vec W hV) = 2 ^ finrank (ZMod 2) (F2Vec W hV) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (F2Vec W hV) = Nat.card W := rfl
  have h3 : 2 ^ finrank (ZMod 2) (F2Vec W hV) < 2 ^ 28 := by
    rw [← h1, h2]
    exact hcard
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h3

theorem j2SmallModules_holds_28 :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ L : Subgroup (MulAut V), IsSporadic .J2 ↥L →
        XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤ → Nat.card V < 2 ^ 28 →
          (FFModel.zornQ j2Γ₀).Realizes L ⊤ ⊥ := by
  intro V _ _ hV L hL hirr hcard
  obtain ⟨θ0⟩ := hL
  let θ : ↥L ≃* G6 := θ0.trans gammaEquiv
  obtain ⟨hntV, hirrU⟩ := CFSG.QuasithinUnique.Bridge.Dichotomy.isIrrOn_of_isIrrSec hirr
  have hfin : FiniteDimensional (ZMod 2) (F2Vec V hV) := Module.Finite.of_finite
  rcases j2_binary_small_28 (F2Vec V hV) (autRepOfJ hV θ) (isIrreducible_autRepOfJ hV θ hirrU)
      (finrank_lt_of_card_lt_28 hV hcard) with he | he
  · obtain ⟨e⟩ := he
    exfalso
    have htriv : ∀ g : G6, g = 1 := by
      intro g
      have h1 : ∀ w : V, (θ.symm g : MulAut V) w = w := by
        intro w
        have h2 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g
          (F2Vec.ofV hV w)
        have h3 : rep1 g = 1 := rfl
        rw [matrixBaseChange_apply, h3, RingHom.coe_id, Matrix.map_id, Matrix.one_mulVec,
          Representation.Equiv.coe_toIntertwiningMap] at h2
        exact Additive.ofMul.injective (e.injective h2)
      have h5 : θ.symm g = 1 := Subtype.ext (MulEquiv.ext h1)
      exact θ.symm.injective (h5.trans (map_one θ.symm).symm)
    obtain ⟨x, y, hxy⟩ := exists_pair_ne G6
    exact hxy ((htriv x).trans (htriv y).symm)
  · obtain ⟨e⟩ := he
    let E : V ≃* W6 :=
      { toFun := fun v => Multiplicative.ofAdd (e (F2Vec.ofV hV v))
        invFun := fun x => F2Vec.toV hV (e.symm (Multiplicative.toAdd x))
        left_inv := fun v => by
          change F2Vec.toV hV (e.symm (e (F2Vec.ofV hV v))) = v
          rw [Representation.Equiv.symm_apply_apply]
          rfl
        right_inv := fun x => by
          change Multiplicative.ofAdd (e (F2Vec.ofV hV (F2Vec.toV hV
            (e.symm (Multiplicative.toAdd x))))) = x
          rw [F2Vec.ofV_toV, Representation.Equiv.apply_symm_apply]
          rfl
        map_mul' := fun a b => by
          simp only [F2Vec.ofV_mul, map_add, ofAdd_add] }
    refine realizes_of_equiv (θ.symm.toMonoidHom.comp qHomΓ)
      (θ.symm.surjective.comp qHomΓ_surjective) E fun γ v => ?_
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (qHomΓ γ)
      (F2Vec.ofV hV v)
    rw [Representation.Equiv.coe_toIntertwiningMap, restrictF4_apply,
      autRepOfJ_apply] at h1
    apply Multiplicative.toAdd.injective
    rw [toAdd_matHom]
    exact h1

end CFSG.Quasithin.J2Mod

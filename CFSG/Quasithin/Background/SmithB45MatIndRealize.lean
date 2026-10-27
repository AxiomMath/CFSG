module

public import CFSG.Quasithin.Background.SmithB45MatM22

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.Quasithin.B45Mat.M22 CFSG.Quasithin.H Module Matrix

section Rep

variable {W : Type} [CommGroup W] (hV : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
  {Γ : Type*} [Group Γ]

@[expose] def autRepOfG (θ : ↥L ≃* Γ) : Representation (ZMod 2) Γ (F2Vec W hV) :=
  (autRep hV).comp (L.subtype.comp θ.symm.toMonoidHom)

theorem autRepOfG_apply (θ : ↥L ≃* Γ) (g : Γ) (v : F2Vec W hV) :
    autRepOfG hV θ g v = F2Vec.ofV hV ((θ.symm g : MulAut W) (F2Vec.toV hV v)) :=
  rfl

theorem irr_autRepOfG (θ : ↥L ≃* Γ)
    (hirr : ∀ U : Subgroup W, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∀ U : Submodule (ZMod 2) (F2Vec W hV), (∀ g, ∀ u ∈ U, autRepOfG hV θ g u ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
  intro U hU
  let U' : Subgroup W :=
    { carrier := {w | F2Vec.ofV hV w ∈ U}
      mul_mem' := fun {a b} ha hb => by
        change F2Vec.ofV hV (a * b) ∈ U
        rw [F2Vec.ofV_mul]
        exact U.add_mem ha hb
      one_mem' := by
        change F2Vec.ofV hV 1 ∈ U
        rw [F2Vec.ofV_one]
        exact U.zero_mem
      inv_mem' := fun {w} hw => by
        have hinv : w⁻¹ = w := by
          rw [inv_eq_iff_mul_eq_one, ← sq]
          exact hV w
        change F2Vec.ofV hV w⁻¹ ∈ U
        rw [hinv]
        exact hw }
  have hU' : ∀ g ∈ L, ∀ u ∈ U', g u ∈ U' := by
    intro g hg u hu
    have h1 := hU (θ ⟨g, hg⟩) _ hu
    change F2Vec.ofV hV ((θ.symm (θ ⟨g, hg⟩) : MulAut W) (F2Vec.toV hV (F2Vec.ofV hV u))) ∈ U
      at h1
    rw [MulEquiv.symm_apply_apply] at h1
    exact h1
  rcases hirr U' hU' with h0 | h0
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hv' : F2Vec.toV hV v ∈ U' := hv
    rw [h0, Subgroup.mem_bot] at hv'
    rw [Submodule.mem_bot, ← F2Vec.ofV_toV hV v, hv', F2Vec.ofV_one]
  · right
    refine eq_top_iff.2 fun v _ => ?_
    have hv' : F2Vec.toV hV v ∈ U' := by
      rw [h0]
      exact Subgroup.mem_top _
    exact hv'

theorem finrank_autRepOfG_le [Finite W] {k : ℕ} (hcard : Nat.card W ≤ 2 ^ k) :
    finrank (ZMod 2) (F2Vec W hV) ≤ k := by
  have h1 : Nat.card (F2Vec W hV) = 2 ^ finrank (ZMod 2) (F2Vec W hV) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (F2Vec W hV) = Nat.card W := rfl
  have h3 : 2 ^ finrank (ZMod 2) (F2Vec W hV) ≤ 2 ^ k := by
    rw [← h1, h2]
    exact hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3

theorem exists_map_congrHom_eq_range' (θ : ↥L ≃* Γ) {n : ℕ}
    (R : Γ →* MulAut (Multiplicative (Fin n → ZMod 2)))
    (e : F2Vec W hV ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (he : ∀ g v, e (F2Vec.ofV hV ((θ.symm g : MulAut W) (F2Vec.toV hV v))) =
      mulAutMat n (R g) *ᵥ e v) :
    ∃ φ : W ≃* Multiplicative (Fin n → ZMod 2), L.map (congrHom φ) = R.range := by
  let φ : W ≃* Multiplicative (Fin n → ZMod 2) :=
    { toFun := fun w => Multiplicative.ofAdd (e (F2Vec.ofV hV w))
      invFun := fun x => F2Vec.toV hV (e.symm (Multiplicative.toAdd x))
      left_inv := fun w => by simp [F2Vec.toV_ofV]
      right_inv := fun x => by simp [F2Vec.ofV_toV]
      map_mul' := fun a b => by
        simp only [F2Vec.ofV_mul, map_add, ofAdd_add] }
  have hφ : ∀ g : Γ, congrHom φ (θ.symm g : MulAut W) = R g := by
    intro g
    refine MulEquiv.ext fun x => ?_
    change Multiplicative.ofAdd (e (F2Vec.ofV hV ((θ.symm g : MulAut W)
      (F2Vec.toV hV (e.symm (Multiplicative.toAdd x)))))) = _
    rw [he, LinearEquiv.apply_symm_apply, mulAutMat_mulVec]
    rfl
  refine ⟨φ, le_antisymm ?_ ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y = (θ.symm (θ ⟨y, hy⟩) : MulAut W) := by rw [MulEquiv.symm_apply_apply]
    rw [hy', hφ]
    exact ⟨_, rfl⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨(θ.symm g : MulAut W), (θ.symm g).2, hφ g⟩

end Rep

end CFSG.Quasithin.B45Mat.Ind

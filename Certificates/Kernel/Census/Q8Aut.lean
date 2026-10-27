module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace Certificates.Census.Q8Aut

open QuaternionGroup

abbrev Q := QuaternionGroup 2

@[expose] def evalW (u v : Q) (w : List Bool) : Q := (w.map fun b => if b then u else v).prod

@[expose] def word : Q → List Bool
  | a 0 => []
  | a 1 => [false, true]
  | a 2 => [true, true]
  | a 3 => [true, false]
  | xa 0 => [true]
  | xa 1 => [false]
  | xa 2 => [true, true, true]
  | xa 3 => [false, false, false]

theorem evalW_word : ∀ g : Q, evalW (xa 0) (xa 1) (word g) = g := by decide +kernel

@[expose] def img (u v : Q) (g : Q) : Q := evalW u v (word g)

theorem map_evalW {F : Type*} [FunLike F Q Q] [MonoidHomClass F Q Q] (σ : F) (u v : Q) (w : List Bool) :
    σ (evalW u v w) = evalW (σ u) (σ v) w := by
  induction w with
  | nil => simp [evalW]
  | cons b w ih =>
    cases b <;> simpa [evalW] using ih

theorem coe_eq_img (σ : MulAut Q) : ⇑σ = img (σ (xa 0)) (σ (xa 1)) := by
  funext g
  conv_lhs => rw [← evalW_word g]
  exact map_evalW σ _ _ _

@[expose] def Adm (u v : Q) : Prop :=
  (∀ g h : Q, img u v (g * h) = img u v g * img u v h) ∧ ∀ g h : Q, img u v g = img u v h → g = h

instance (u v : Q) : Decidable (Adm u v) := by unfold Adm; infer_instance

theorem adm (σ : MulAut Q) : Adm (σ (xa 0)) (σ (xa 1)) := by
  rw [Adm, ← coe_eq_img]
  exact ⟨fun g h => map_mul σ g h, fun g h hgh => σ.injective hgh⟩

theorem forall_of_adm (P : (Q → Q) → Prop) (h : ∀ u v : Q, Adm u v → P (img u v)) (σ : MulAut Q) :
    P σ := by
  rw [coe_eq_img]
  exact h _ _ (adm σ)

theorem forall₂_of_adm (P : (Q → Q) → (Q → Q) → Prop)
    (h : ∀ u v : Q, Adm u v → ∀ u' v' : Q, Adm u' v' → P (img u v) (img u' v')) (σ γ : MulAut Q) :
    P σ γ := by
  rw [coe_eq_img σ, coe_eq_img γ]
  exact h _ _ (adm σ) _ _ (adm γ)

theorem img_x (u v : Q) : img u v (xa 0) = u := by simp [img, word, evalW]

theorem img_y (u v : Q) : img u v (xa 1) = v := by simp [img, word, evalW]

noncomputable def ofAdm (u v : Q) (h : Adm u v) : MulAut Q :=
  MulEquiv.ofBijective (MonoidHom.mk' (img u v) h.1)
    ⟨h.2, Finite.surjective_of_injective (f := img u v) h.2⟩

noncomputable def mulAutEquiv : MulAut Q ≃ {p : Q × Q // Adm p.1 p.2} where
  toFun σ := ⟨(σ (xa 0), σ (xa 1)), adm σ⟩
  invFun p := ofAdm p.1.1 p.1.2 p.2
  left_inv σ := by
    ext g
    change img _ _ g = σ g
    rw [coe_eq_img σ]
  right_inv p := by
    ext
    · exact img_x _ _
    · exact img_y _ _

theorem card_adm : Fintype.card {p : Q × Q // Adm p.1 p.2} = 24 := by decide +kernel

theorem card_mulAut : Nat.card (MulAut Q) = 24 := by
  rw [Nat.card_congr mulAutEquiv, Nat.card_eq_fintype_card, card_adm]

theorem inner_of_mul_self (σ : MulAut Q) (h : ∀ q, σ q * q = 1 ∨ σ q * q = a 2) :
    ∃ q0, ∀ x, σ x = q0 * x * q0⁻¹ :=
  forall_of_adm (fun f => (∀ q, f q * q = 1 ∨ f q * q = a 2) → ∃ q0, ∀ x, f x = q0 * x * q0⁻¹)
    (by decide +kernel) σ h

theorem fixed_of_outer : ∀ σ : MulAut Q, (∀ y, σ (σ y) = y) →
    ¬ (∃ q : Q, ∀ y, σ y = q * y * q⁻¹) → ∀ x, σ x = x → x = 1 ∨ x = a 2 :=
  forall_of_adm (fun f => (∀ y, f (f y) = y) → ¬ (∃ q : Q, ∀ y, f y = q * y * q⁻¹) →
    ∀ x, f x = x → x = 1 ∨ x = a 2) (by decide +kernel)

@[expose] def Outer2 (f : Q → Q) : Prop := (∀ y, f (f y) = y) ∧ ¬ ∃ q : Q, ∀ y, f y = q * y * q⁻¹

@[expose] def Ord3 (g : Q → Q) : Prop := (∀ y, g (g (g y)) = y) ∧ ∃ y, g y ≠ y

@[expose] def CommF (f g : Q → Q) : Prop := ∀ y, f (g y) = g (f y)

instance (f : Q → Q) : Decidable (Outer2 f) := by unfold Outer2; infer_instance
instance (g : Q → Q) : Decidable (Ord3 g) := by unfold Ord3; infer_instance
instance (f g : Q → Q) : Decidable (CommF f g) := by unfold CommF; infer_instance

theorem no_comm_adm : ∀ u v : Q, Adm u v → Outer2 (img u v) → ∀ u' v' : Q, Adm u' v' →
    Ord3 (img u' v') → ¬ CommF (img u v) (img u' v') := by decide +kernel

theorem no_comm_of_outer : ∀ σ γ : MulAut Q, (∀ y, σ (σ y) = y) →
    ¬ (∃ q : Q, ∀ y, σ y = q * y * q⁻¹) → (∀ y, γ (γ (γ y)) = y) →
    (∃ y, γ y ≠ y) → ¬ (∀ y, σ (γ y) = γ (σ y)) :=
  forall₂_of_adm (fun f g => (∀ y, f (f y) = y) → ¬ (∃ q : Q, ∀ y, f y = q * y * q⁻¹) →
    (∀ y, g (g (g y)) = y) → (∃ y, g y ≠ y) → ¬ (∀ y, f (g y) = g (f y)))
    (fun u v h u' v' h' h1 h2 h3 h4 =>
      no_comm_adm u v h ⟨h1, h2⟩ u' v' h' ⟨h3, h4⟩)

theorem twisted_of_outer : ∀ σ : MulAut Q, (∀ y, σ (σ y) = y) →
    ¬ (∃ q : Q, ∀ y, σ y = q * y * q⁻¹) → ∀ q, q * σ q = 1 → ∃ d, q = d * (σ d)⁻¹ :=
  forall_of_adm (fun f => (∀ y, f (f y) = y) → ¬ (∃ q : Q, ∀ y, f y = q * y * q⁻¹) →
    ∀ q, q * f q = 1 → ∃ d, q = d * (f d)⁻¹) (by decide +kernel)

theorem neg_card : Fintype.card {p : Q × Q // Adm p.1 p.2} ≠ 23 := by decide +kernel

theorem neg_inner : ¬ ∀ u v : Q, Adm u v → ∃ q0, ∀ x, img u v x = q0 * x * q0⁻¹ := by
  decide +kernel

theorem neg_fixed : ¬ ∀ u v : Q, Adm u v → ∀ x, img u v x = x → x = 1 := by decide +kernel

end Certificates.Census.Q8Aut

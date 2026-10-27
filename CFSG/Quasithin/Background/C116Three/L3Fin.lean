module

public import CFSG.Quasithin.Background.B4L3Fin

public section

namespace CFSG.Quasithin.C116Three.L3F

open CFSG.Quasithin.L3

@[expose] def e1 : Vec := ![1, 0, 0]

@[expose] def plane12 : Finset Vec := Finset.univ.filter fun x => x 2 = 0

@[expose] def Ppt (γ : Γ) : Prop := act γ e1 = e1

instance : DecidablePred Ppt := fun γ => by unfold Ppt; infer_instance

@[expose] def Pline (γ : Γ) : Prop := ∀ x ∈ plane12, act γ x ∈ plane12

instance : DecidablePred Pline := fun γ => by unfold Pline; infer_instance

@[expose] def Ustd (γ : Γ) : Prop := Ppt γ ∧ Pline γ

instance : DecidablePred Ustd := fun γ => by unfold Ustd; infer_instance

@[expose] def B1 : Finset Γ := BS plane12

@[expose] def B2 : Finset Γ := AS {0, e1}

theorem e1_ne_zero : e1 ≠ 0 := by
  unfold e1
  decide

theorem isPlane_plane12 : IsPlane plane12 := by
  unfold plane12
  decide +kernel

theorem mem_B1 {γ : Γ} : γ ∈ B1 ↔ ∀ x ∈ plane12, act γ x = x := by
  simp [B1, BS]

set_option maxRecDepth 100000 in
theorem card_U : (Finset.univ.filter Ustd).card = 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem card_B1 : B1.card = 4 := by unfold B1; decide +kernel

set_option maxRecDepth 100000 in
theorem card_B2 : B2.card = 4 := by unfold B2; decide +kernel

set_option maxRecDepth 100000 in
theorem B2_comm : ∀ b ∈ B2, ∃ p q : Γ, Ppt p ∧ Ppt q ∧ b * (q * p) = p * q := by
  unfold B2; decide +kernel

set_option maxRecDepth 100000 in
theorem B1_fix : ∀ x : Vec, (∀ b ∈ B1, act b x = x) → x ∈ plane12 := by
  unfold B1; decide +kernel

set_option maxRecDepth 100000 in
theorem Pline_trans : ∀ x ∈ plane12, x ≠ 0 → ∃ p : Γ, Pline p ∧ act p x = e1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem Pline_norm : ∀ p : Γ, Pline p → ∀ b ∈ B1, ∃ b' ∈ B1, b * p = p * b' := by
  unfold B1; decide +kernel

set_option maxRecDepth 100000 in
private theorem U_comm_aux : ∀ s : Γ, ∀ t : Γ,
    (Ustd s ∧ s * s = 1 ∧ Ustd t ∧ t * t = 1 ∧ s * t = t * s) →
    (s ∈ B1 ∧ t ∈ B1) ∨ (s ∈ B2 ∧ t ∈ B2) := by
  unfold B1 B2; decide +kernel

theorem U_comm : ∀ s : Γ, Ustd s → s * s = 1 → ∀ t : Γ, Ustd t → t * t = 1 → s * t = t * s →
    (s ∈ B1 ∧ t ∈ B1) ∨ (s ∈ B2 ∧ t ∈ B2) :=
  fun s hs hs2 t ht ht2 hst => U_comm_aux s t ⟨hs, hs2, ht, ht2, hst⟩

set_option maxRecDepth 100000 in
theorem fixS_card_le : ∀ t : Γ, t ≠ 1 → (fixS t).card ≤ 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem B2_fix : ∀ x : Vec, (∀ b ∈ B2, act b x = x) → x = 0 ∨ x = e1 := by
  unfold B2; decide +kernel

set_option maxRecDepth 100000 in
theorem B2_fix_e1 : ∀ b ∈ B2, act b e1 = e1 := by unfold B2; decide +kernel

theorem exists_move : ∃ γ : Γ, act γ e1 ≠ e1 := act_nofix e1 e1_ne_zero

end CFSG.Quasithin.C116Three.L3F

module

public import CFSG.Timmesfeld.Transvection.RelBuildBasic

public section

namespace CFSG.Timmesfeld.Transvection.RelBuild

open CFSG.Timmesfeld.Transvection.Pres
open scoped commutatorElement

variable {r : ℕ} {F : Type*} [Field F] {G : Type*} [Group G]

@[expose] def wPos (w : Fin r → G) (a : Fin r ⊕ Fin r) : G :=
  Sum.elim (fun _ => 1) w a

@[expose] def wNeg (w : Fin r → G) (b : Fin r ⊕ Fin r) : G :=
  Sum.elim w (fun _ => 1) b

@[expose] def familyLT (β : Fin r → Fin r → F → G) (w : Fin r → G) (a b : Fin r ⊕ Fin r)
    (c : F) : G :=
  wPos w a * wNeg w b * β (idx b) (idx a) c * (wPos w a * wNeg w b)⁻¹

@[expose] noncomputable def family (σ : F ≃+* F) (β : Fin r → Fin r → F → G) (w : Fin r → G)
    (a b : Fin r ⊕ Fin r) (c : F) : G :=
  if idx b < idx a then familyLT β w a b c
  else if idx a < idx b then familyLT β w b a (σ c) else 1

variable {σ : F ≃+* F} {β : Fin r → Fin r → F → G} {w : Fin r → G}

theorem family_of_lt {a b : Fin r ⊕ Fin r} (h : idx b < idx a) (c : F) :
    family σ β w a b c = familyLT β w a b c :=
  ite_eq_left h

theorem family_of_gt {a b : Fin r ⊕ Fin r} (h : idx a < idx b) (c : F) :
    family σ β w a b c = familyLT β w b a (σ c) := by
  rw [family, ite_eq_right (not_lt.2 h.le), ite_eq_left h]

@[simp] theorem family_inl_inr {i j : Fin r} (h : i < j) (c : F) :
    family σ β w (.inl j) (.inr i) c = β i j c := by
  rw [family_of_lt (by simpa using h)]
  simp [familyLT, wPos, wNeg]

@[simp] theorem family_inl_inl {i j : Fin r} (h : i < j) (c : F) :
    family σ β w (.inl j) (.inl i) c = w i * β i j c * (w i)⁻¹ := by
  rw [family_of_lt (by simpa using h)]
  simp [familyLT, wPos, wNeg]

@[simp] theorem family_inr_inr {i j : Fin r} (h : i < j) (c : F) :
    family σ β w (.inr j) (.inr i) c = w j * β i j c * (w j)⁻¹ := by
  rw [family_of_lt (by simpa using h)]
  simp [familyLT, wPos, wNeg]

@[simp] theorem family_inr_inl {i j : Fin r} (h : i < j) (c : F) :
    family σ β w (.inr j) (.inl i) c = w j * w i * β i j c * (w j * w i)⁻¹ := by
  rw [family_of_lt (by simpa using h)]
  simp [familyLT, wPos, wNeg]

theorem family_swap (hσ : ∀ c, σ (σ c) = c) {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b)
    (c : F) : family σ β w b a c = family σ β w a b (σ c) := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [family_of_lt h, family_of_gt h, hσ]
  · rw [family_of_gt h, family_of_lt h]

theorem family_add (hβ : ∀ i j : Fin r, i < j → ∀ s t, β i j (s + t) = β i j s * β i j t)
    {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) (s t : F) :
    family σ β w a b (s + t) = family σ β w a b s * family σ β w a b t := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [family_of_gt h, family_of_gt h, family_of_gt h, map_add]
    simp only [familyLT, hβ _ _ h]
    group
  · rw [family_of_lt h, family_of_lt h, family_of_lt h]
    simp only [familyLT, hβ _ _ h]
    group

theorem family_injective (hβ : ∀ i j : Fin r, i < j → Function.Injective (β i j))
    {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) : Function.Injective (family σ β w a b) := by
  intro s t hst
  rcases lt_or_gt_of_ne hab with h | h
  · rw [family_of_gt h, family_of_gt h] at hst
    simp only [familyLT, mul_left_inj, mul_right_inj] at hst
    exact σ.injective (hβ _ _ h hst)
  · rw [family_of_lt h, family_of_lt h] at hst
    simp only [familyLT, mul_left_inj, mul_right_inj] at hst
    exact hβ _ _ h hst

theorem conj_conj (g h x : G) : g * (h * x * h⁻¹) * g⁻¹ = g * h * x * (g * h)⁻¹ := by
  group

theorem mul_wPos (hw : ∀ i, w i * w i = 1) {k : Fin r} {a : Fin r ⊕ Fin r} (h : idx a = k) :
    w k * wPos w a = wPos w (flip k a) := by
  rw [flip_of_idx_eq h]
  rcases a with i | i <;> simp only [idx_inl, idx_inr] at h <;> subst h <;>
    simp [wPos, hw]

theorem mul_wNeg (hw : ∀ i, w i * w i = 1) {k : Fin r} {b : Fin r ⊕ Fin r} (h : idx b = k) :
    w k * wNeg w b = wNeg w (flip k b) := by
  rw [flip_of_idx_eq h]
  rcases b with i | i <;> simp only [idx_inl, idx_inr] at h <;> subst h <;>
    simp [wNeg, hw]

theorem commute_wPos (hwc : ∀ i j, w i * w j = w j * w i) (k : Fin r) (a : Fin r ⊕ Fin r) :
    w k * wPos w a = wPos w a * w k := by
  rcases a with i | i <;> simp [wPos, hwc]

theorem commute_wNeg (hwc : ∀ i j, w i * w j = w j * w i) (k : Fin r) (b : Fin r ⊕ Fin r) :
    w k * wNeg w b = wNeg w b * w k := by
  rcases b with i | i <;> simp [wNeg, hwc]

omit [Field F] in
theorem weyl_familyLT (hw : ∀ i, w i * w i = 1) (hwc : ∀ i j, w i * w j = w j * w i)
    (hwβ : ∀ i j k : Fin r, i < j → k ≠ i → k ≠ j → ∀ c, w k * β i j c = β i j c * w k)
    {a b : Fin r ⊕ Fin r} (hab : idx b < idx a) (k : Fin r) (c : F) :
    w k * familyLT β w a b c * (w k)⁻¹ = familyLT β w (flip k a) (flip k b) c := by
  simp only [familyLT, idx_flip]
  rw [conj_conj]
  by_cases hka : idx a = k
  · have hW : w k * (wPos w a * wNeg w b) = wPos w (flip k a) * wNeg w (flip k b) := by
      rw [flip_of_idx_ne (show idx b ≠ k by omega), ← mul_wPos hw hka, mul_assoc]
    rw [hW]
  by_cases hkb : idx b = k
  · have hW : w k * (wPos w a * wNeg w b) = wPos w (flip k a) * wNeg w (flip k b) := by
      rw [flip_of_idx_ne hka, ← mul_wNeg hw hkb, ← mul_assoc, commute_wPos hwc, mul_assoc]
    rw [hW]
  rw [flip_of_idx_ne hka, flip_of_idx_ne hkb]
  have hW : w k * (wPos w a * wNeg w b) = wPos w a * wNeg w b * w k := by
    rw [← mul_assoc, commute_wPos hwc, mul_assoc, commute_wNeg hwc, mul_assoc]
  have hβk := hwβ (idx b) (idx a) k hab (Ne.symm hkb) (Ne.symm hka) c
  rw [hW]
  calc wPos w a * wNeg w b * w k * β (idx b) (idx a) c * (wPos w a * wNeg w b * w k)⁻¹ =
        wPos w a * wNeg w b * (w k * β (idx b) (idx a) c) * (w k)⁻¹ *
          (wPos w a * wNeg w b)⁻¹ := by group
    _ = _ := by rw [hβk]; group

theorem family_weyl (hw : ∀ i, w i * w i = 1) (hwc : ∀ i j, w i * w j = w j * w i)
    (hwβ : ∀ i j k : Fin r, i < j → k ≠ i → k ≠ j → ∀ c, w k * β i j c = β i j c * w k)
    {a b : Fin r ⊕ Fin r} (hab : idx a ≠ idx b) (k : Fin r) (c : F) :
    w k * family σ β w a b c * (w k)⁻¹ = family σ β w (flip k a) (flip k b) c := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [family_of_gt h, family_of_gt (by simpa using h), weyl_familyLT hw hwc hwβ h]
  · rw [family_of_lt h, family_of_lt (by simpa using h), weyl_familyLT hw hwc hwβ h]

end CFSG.Timmesfeld.Transvection.RelBuild

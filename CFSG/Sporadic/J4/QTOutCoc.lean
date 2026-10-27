module

public import CFSG.Sporadic.J4.QTOutAct
public import CFSG.Sporadic.J4.QTOutCocCheck

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native

section Masks

variable (hM : MatFacts)

theorem exists_mask (hF : J4Facts) (α : MulAut J) (hH : ∀ x, α x ∈ Hj ↔ x ∈ Hj)
    (hfix : ∀ c < 2 ^ 11, α (eta uJ 11 c) = eta uJ 11 c) {h : J} (hh : h ∈ Hj) :
    ∃ e < 2 ^ 11, α h = eta uJ 11 e * h := by
  have hM := hF.mat
  have hu : α h * h⁻¹ ∈ Eg uJ 11 := by
    refine centralizer_Hj hM hF _ (Hj.mul_mem ((hH h).2 hh) (Hj.inv_mem hh)) (fun y hy => ?_)
    obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
    obtain ⟨c', hc', hcc'⟩ := (mem_Eg_iff (elem_uJ hM)).1
      (Hj_normalizes_Eg hM h⁻¹ (Hj.inv_mem hh) _ (eta_mem_Eg 11 le_rfl c))
    have e1 : eta uJ 11 c = h * eta uJ 11 c' * h⁻¹ := by
      rw [← hcc']
      group
    have e2 := congrArg α e1
    rw [hfix c hc, map_mul, map_mul, map_inv, hfix c' hc'] at e2
    calc α h * h⁻¹ * eta uJ 11 c
        = α h * (h⁻¹ * eta uJ 11 c * h) * h⁻¹ := by group
      _ = α h * eta uJ 11 c' * h⁻¹ := by
        rw [show h⁻¹ * eta uJ 11 c * h = eta uJ 11 c' by simpa using hcc']
      _ = (α h * eta uJ 11 c' * (α h)⁻¹) * (α h * h⁻¹) := by group
      _ = eta uJ 11 c * (α h * h⁻¹) := by rw [← e2]
  obtain ⟨e, he, hee⟩ := (mem_Eg_iff (elem_uJ hM)).1 hu
  refine ⟨e, he, ?_⟩
  rw [← hee]
  group

theorem cocW_cons (d : ℤ → ℕ) (ℓ : ℤ) (w : List ℤ) : cocW d (ℓ :: w) = d ℓ ^^^ act ℓ (cocW d w) :=
  rfl

theorem cocW_nil (d : ℤ → ℕ) : cocW d [] = 0 := rfl

theorem cocW_congr {d d' : ℤ → ℕ} : ∀ {w : List ℤ}, (∀ ℓ ∈ w, d ℓ = d' ℓ) → cocW d w = cocW d' w
  | [], _ => rfl
  | ℓ :: w, h => by
    rw [cocW_cons, cocW_cons, h ℓ (List.mem_cons_self ..),
      cocW_congr (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem act_lt {ℓ : ℤ} (hℓ : ℓ ∈ letters) (c : ℕ) : act ℓ c < 2 ^ 11 := by
  rw [← actT_letterTab]
  exact actT_lt (letterTab_ok ℓ hℓ) c

theorem dLet_lt {e0 e1 e2 : ℕ} (h0 : e0 < 2 ^ 11) (h1 : e1 < 2 ^ 11) (h2 : e2 < 2 ^ 11) {ℓ : ℤ}
    (hℓ : ℓ ∈ letters) : dLet e0 e1 e2 ℓ < 2 ^ 11 := by
  rcases letters_cases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [dLet] using h0
  · simpa [dLet] using h1
  · simpa [dLet] using h2
  · simpa [dLet] using act_lt hℓ e0
  · simpa [dLet] using act_lt hℓ e1
  · simpa [dLet] using act_lt hℓ e2

theorem cocW_lt {d : ℤ → ℕ} (hd : ∀ ℓ ∈ letters, d ℓ < 2 ^ 11) :
    ∀ {w : List ℤ}, (∀ ℓ ∈ w, ℓ ∈ letters) → cocW d w < 2 ^ 11
  | [], _ => by rw [cocW_nil]; exact Nat.two_pow_pos 11
  | ℓ :: w, h => by
    rw [cocW_cons]
    have hℓ := h ℓ (List.mem_cons_self ..)
    exact lt_xor (hd ℓ hℓ) (act_lt hℓ _)

include hM

theorem alpha_letter (α : MulAut J) {e0 e1 e2 : ℕ}
    (h0 : α (xJ 0) = eta uJ 11 e0 * xJ 0) (h1 : α (xJ 1) = eta uJ 11 e1 * xJ 1)
    (h2 : α (xJ 2) = eta uJ 11 e2 * xJ 2) {ℓ : ℤ} (hℓ : ℓ ∈ letters) :
    α (XJ ℓ) = eta uJ 11 (dLet e0 e1 e2 ℓ) * XJ ℓ := by
  have inv_case : ∀ (g : J) (e : ℕ) (k : ℤ), (-k) ∈ letters → XJ (-k) = g⁻¹ →
      α g = eta uJ 11 e * g →
      α (XJ (-k)) = eta uJ 11 (act (-k) e) * XJ (-k) := by
    intro g e k hk hXk hg
    rw [hXk, map_inv, hg]
    have h1 := hX_all hM hk e
    rw [hXk] at h1
    have h2 : (eta uJ 11 e * g)⁻¹ = g⁻¹ * eta uJ 11 e := by
      rw [mul_inv_rev, eta_inv_self hM]
    rw [h2, ← h1]
    group
  rcases letters_cases hℓ with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [XJ_one, h0]; simp [dLet]
  · rw [XJ_two, h1]; simp [dLet]
  · rw [XJ_three, h2]; simp [dLet]
  · have := inv_case (xJ 0) e0 1 (by decide) XJ_neg_one h0
    simpa [dLet] using this
  · have := inv_case (xJ 1) e1 2 (by decide) XJ_neg_two h1
    simpa [dLet] using this
  · have := inv_case (xJ 2) e2 3 (by decide) XJ_neg_three h2
    simpa [dLet] using this

theorem alpha_word (α : MulAut J) {e0 e1 e2 : ℕ}
    (h0 : α (xJ 0) = eta uJ 11 e0 * xJ 0) (h1 : α (xJ 1) = eta uJ 11 e1 * xJ 1)
    (h2 : α (xJ 2) = eta uJ 11 e2 * xJ 2) :
    ∀ {w : List ℤ}, (∀ ℓ ∈ w, ℓ ∈ letters) →
      α (wordProd xJ w) = eta uJ 11 (cocW (dLet e0 e1 e2) w) * wordProd xJ w
  | [], _ => by
    have h1 : wordProd xJ ([] : List ℤ) = 1 := rfl
    rw [h1, cocW_nil, eta_zero, map_one, one_mul]
  | ℓ :: w, h => by
    have hℓ := h ℓ (List.mem_cons_self ..)
    have ih := alpha_word α h0 h1 h2 (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [wordProd_xJ, List.map_cons, List.prod_cons, map_mul, alpha_letter hM α h0 h1 h2 hℓ,
      ← wordProd_xJ, ih, cocW_cons]
    have hconj := hX_all hM hℓ (cocW (dLet e0 e1 e2) w)
    rw [eta_xor (elem_uJ hM) le_rfl]
    calc eta uJ 11 (dLet e0 e1 e2 ℓ) * XJ ℓ *
          (eta uJ 11 (cocW (dLet e0 e1 e2) w) * wordProd xJ w)
        = eta uJ 11 (dLet e0 e1 e2 ℓ) *
          (XJ ℓ * eta uJ 11 (cocW (dLet e0 e1 e2) w) * (XJ ℓ)⁻¹) * (XJ ℓ * wordProd xJ w) := by
          group
      _ = eta uJ 11 (dLet e0 e1 e2 ℓ) * eta uJ 11 (act ℓ (cocW (dLet e0 e1 e2) w)) *
          (XJ ℓ * wordProd xJ w) := by rw [hconj]
      _ = _ := rfl

end Masks

theorem wordProd_mem_Eg_of_table (hF : J4Facts) {w : List ℤ} (hw : ∀ ℓ ∈ w, ℓ ∈ letters)
    (ht : wordT w = idT) : wordProd xJ w ∈ Eg uJ 11 := by
  have hM := hF.mat
  have hA := Acts_wordProd hM w hw
  rw [ht] at hA
  refine centralizer_Hj hM hF _ (wordProd_mem_Hj hw) (fun y hy => ?_)
  obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hy
  have h1 := hA.2 c hc
  rw [actT_idT hc] at h1
  calc wordProd xJ w * eta uJ 11 c
      = (wordProd xJ w * eta uJ 11 c * (wordProd xJ w)⁻¹) * wordProd xJ w := by group
    _ = eta uJ 11 c * wordProd xJ w := by rw [h1]

theorem cocW_rel (hF : J4Facts) (α : MulAut J)
    (hfix : ∀ c < 2 ^ 11, α (eta uJ 11 c) = eta uJ 11 c) {e0 e1 e2 : ℕ}
    (e0lt : e0 < 2 ^ 11) (e1lt : e1 < 2 ^ 11) (e2lt : e2 < 2 ^ 11)
    (h0 : α (xJ 0) = eta uJ 11 e0 * xJ 0) (h1 : α (xJ 1) = eta uJ 11 e1 * xJ 1)
    (h2 : α (xJ 2) = eta uJ 11 e2 * xJ 2) {r : List ℤ} (hr : r ∈ rel01 ++ rel02 ++ relMix) :
    cocW (dLet e0 e1 e2) r = 0 := by
  have hM := hF.mat
  have hl : ∀ ℓ ∈ r, ℓ ∈ letters := rel_letters r hr
  obtain ⟨c, hc, hcr⟩ := (mem_Eg_iff (elem_uJ hM)).1
    (wordProd_mem_Eg_of_table hF hl (rel_tables r hr))
  have hw := alpha_word hM α h0 h1 h2 hl
  rw [hcr, hfix c hc] at hw
  have hone : eta uJ 11 (cocW (dLet e0 e1 e2) r) = 1 := by
    have : eta uJ 11 (cocW (dLet e0 e1 e2) r) * eta uJ 11 c = 1 * eta uJ 11 c := by
      rw [one_mul]; exact hw.symm
    exact mul_right_cancel this
  by_contra hne
  exact eta_ne_one hM hne (cocW_lt (fun ℓ hℓ => dLet_lt e0lt e1lt e2lt hℓ) hl) hone

theorem classify_masks (hF : J4Facts) (α : MulAut J)
    (hfix : ∀ c < 2 ^ 11, α (eta uJ 11 c) = eta uJ 11 c) {e1 e2 : ℕ}
    (e1lt : e1 < 2 ^ 11) (e2lt : e2 < 2 ^ 11)
    (h0 : α (xJ 0) = eta uJ 11 0 * xJ 0) (h1 : α (xJ 1) = eta uJ 11 e1 * xJ 1)
    (h2 : α (xJ 2) = eta uJ 11 e2 * xJ 2) :
    (e1 = 0 ∧ e2 = 0) ∨ (e1 = 1373 ∧ e2 = 689) := by
  have hall : ∀ r ∈ rel01 ++ rel02 ++ relMix, cocW (dLet 0 e1 e2) r = 0 := fun r hr =>
    cocW_rel hF α hfix (Nat.two_pow_pos 11) e1lt e2lt h0 h1 h2 hr
  have hs1 : e1 ∈ stage1 := by
    unfold stage1
    rw [List.mem_filter]
    refine ⟨List.mem_range.2 (by simpa using e1lt), ?_⟩
    rw [List.all_eq_true]
    intro r hr
    have hrl := rel01_letters r hr
    have := hall r (by simp [hr])
    have hc : cocW (dLet 0 e1 e2) r = cocW (dLet 0 e1 0) r := by
      apply cocW_congr
      intro ℓ hℓ
      rcases hrl ℓ hℓ with rfl | rfl | rfl | rfl <;> simp [dLet]
    rw [← hc, this]
    simp
  have hs2 : e2 ∈ stage2 := by
    unfold stage2
    rw [List.mem_filter]
    refine ⟨List.mem_range.2 (by simpa using e2lt), ?_⟩
    rw [List.all_eq_true]
    intro r hr
    have hrl := rel02_letters r hr
    have := hall r (by simp [hr])
    have hc : cocW (dLet 0 e1 e2) r = cocW (dLet 0 0 e2) r := by
      apply cocW_congr
      intro ℓ hℓ
      rcases hrl ℓ hℓ with rfl | rfl | rfl | rfl <;> simp [dLet]
    rw [← hc, this]
    simp
  rw [stage1_eq] at hs1
  rw [stage2_eq] at hs2
  have hrel : relAll e1 e2 = true := by
    unfold relAll
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    refine ⟨⟨fun r hr => hall r (by simp [hr]), fun r hr => hall r (by simp [hr])⟩,
      fun r hr => hall r (by simp [hr])⟩
  obtain ⟨c1, c2, c3, c4⟩ := relAll_cases
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs1 hs2
  rcases hs1 with rfl | rfl <;> rcases hs2 with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · rw [c3] at hrel; exact absurd hrel (by decide)
  · rw [c4] at hrel; exact absurd hrel (by decide)
  · exact Or.inr ⟨rfl, rfl⟩

theorem classify_gens (hF : J4Facts) (α : MulAut J)
    (hE : ∀ x, α x ∈ Eg uJ 11 ↔ x ∈ Eg uJ 11) (hH : ∀ x, α x ∈ Hj ↔ x ∈ Hj)
    (hfix : ∀ c < 2 ^ 11, α (eta uJ 11 c) = eta uJ 11 c) :
    ∃ β : MulAut J, (∃ v < 2 ^ 11, ∀ x, β x = eta uJ 11 v * α x * eta uJ 11 v) ∧
      (∀ x, β x ∈ Eg uJ 11 ↔ x ∈ Eg uJ 11) ∧ (∀ x, β x ∈ Hj ↔ x ∈ Hj) ∧
      (∀ c < 2 ^ 11, β (eta uJ 11 c) = eta uJ 11 c) ∧
      ((β (xJ 0) = xJ 0 ∧ β (xJ 1) = xJ 1 ∧ β (xJ 2) = xJ 2) ∨
        (β (xJ 0) = xJ 0 ∧ β (xJ 1) = eta uJ 11 1373 * xJ 1 ∧
          β (xJ 2) = eta uJ 11 689 * xJ 2)) := by
  have hM := hF.mat
  obtain ⟨e0, he0, h0⟩ := exists_mask hF α hH hfix (xJ_mem (k := 0) (by norm_num))
  obtain ⟨v, hv, hvx⟩ := t0_surj e0 he0
  have hvH : eta uJ 11 v ∈ Hj := Eg_le_Hj (eta_mem_Eg 11 le_rfl v)
  obtain ⟨β, hβ⟩ : ∃ β : MulAut J, ∀ x, β x = eta uJ 11 v * α x * eta uJ 11 v :=
    ⟨twistAut (eta uJ 11 v) α, fun x => by
      rw [twistAut_apply, eta_inv_self hM]⟩
  have hβ' : ∀ x, β x = (eta uJ 11 v)⁻¹ * α x * eta uJ 11 v := fun x => by
    rw [hβ, eta_inv_self hM]
  have hEβ : ∀ x, β x ∈ Eg uJ 11 ↔ x ∈ Eg uJ 11 := fun x => by
    rw [hβ', twist_mem_Eg hM hvH, hE]
  have hHβ : ∀ x, β x ∈ Hj ↔ x ∈ Hj := fun x => by
    rw [hβ', twist_mem_Hj hvH, hH]
  have hfixβ : ∀ c < 2 ^ 11, β (eta uJ 11 c) = eta uJ 11 c := fun c hc => by
    rw [hβ, hfix c hc]
    calc eta uJ 11 v * eta uJ 11 c * eta uJ 11 v
        = (eta uJ 11 v * eta uJ 11 c) * eta uJ 11 v := rfl
      _ = (eta uJ 11 c * eta uJ 11 v) * eta uJ 11 v := by rw [eta_comm (elem_uJ hM)]
      _ = eta uJ 11 c := by rw [mul_assoc, eta_sq (elem_uJ hM), mul_one]
  have hβ0 : β (xJ 0) = xJ 0 := by
    have hx := Acts_xJ_zero hM
    have e1 := hx.2 v hv
    have e2 : eta uJ 11 v * (eta uJ 11 e0 * xJ 0) * eta uJ 11 v =
        eta uJ 11 (v ^^^ e0 ^^^ actT t0 v) * xJ 0 := by
      rw [eta_xor (elem_uJ hM) le_rfl, eta_xor (elem_uJ hM) le_rfl, ← e1]
      group
    have e3 : v ^^^ e0 ^^^ actT t0 v = 0 := by
      have h' : actT t0 v = actT (letterTab 1) v := rfl
      rw [h', ← hvx, Nat.xor_xor_cancel_left, Nat.xor_self]
    rw [hβ, h0, e2, e3, eta_zero, one_mul]
  have hlt1 : ∃ e < 2 ^ 11, β (xJ 1) = eta uJ 11 e * xJ 1 :=
    exists_mask hF β hHβ hfixβ (xJ_mem (k := 1) (by norm_num))
  have hlt2 : ∃ e < 2 ^ 11, β (xJ 2) = eta uJ 11 e * xJ 2 :=
    exists_mask hF β hHβ hfixβ (xJ_mem (k := 2) (by norm_num))
  obtain ⟨e1, he1, h1⟩ := hlt1
  obtain ⟨e2, he2, h2⟩ := hlt2
  have hβ0' : β (xJ 0) = eta uJ 11 0 * xJ 0 := by rw [hβ0, eta_zero, one_mul]
  refine ⟨β, ⟨v, hv, hβ⟩, hEβ, hHβ, hfixβ, ?_⟩
  rcases classify_masks hF β hfixβ he1 he2 hβ0' h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    exact ⟨hβ0, by rw [h1, eta_zero, one_mul], by rw [h2, eta_zero, one_mul]⟩
  · right
    exact ⟨hβ0, h1, h2⟩

end CFSG.Sporadic.J4.QT

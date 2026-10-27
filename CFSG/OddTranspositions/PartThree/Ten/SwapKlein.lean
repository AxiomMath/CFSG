module

public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.OddTranspositions.PartThree.Ten.WreathClass
import CFSG.Timmesfeld.Bridge.Asc72Bender

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

namespace SwapKlein

open Equiv SemidirectProduct WreathEndgame

variable {f m : ℕ}

theorem exists_klein_psl2 (hf : 2 ≤ f) :
    ∃ t c : PSL2Model f, t * t = 1 ∧ c * c = 1 ∧ t * c = c * t ∧ t ≠ 1 ∧ c ≠ 1 ∧ t ≠ c := by
  have hK : IsBenderGroup (PSL2Model f) := IsBenderGroup.isPSL2 f hf (MulEquiv.refl _)
  obtain ⟨Q⟩ : Nonempty (Sylow 2 (PSL2Model f)) := inferInstance
  have hcard := IsBenderGroup.four_le_card_center hK Q
  have hab := IsBenderGroup.commute_of_psl2 hf (MulEquiv.refl (PSL2Model f)) Q
  set Z := Subgroup.center (Q : Subgroup (PSL2Model f)) with hZ
  have hsq : ∀ z : Z, ((z : Q) : PSL2Model f) * ((z : Q) : PSL2Model f) = 1 := fun z =>
    IsBenderGroup.mul_self_eq_one_of_commute hK Q (z : Q).2 fun y hy =>
      (hab _ (z : Q).2 y hy)
  have hcomm : ∀ z z' : Z, ((z : Q) : PSL2Model f) * ((z' : Q) : PSL2Model f) =
      ((z' : Q) : PSL2Model f) * ((z : Q) : PSL2Model f) := fun z z' =>
    hab _ (z : Q).2 _ (z' : Q).2 |>.eq
  have : Fintype Z := Fintype.ofFinite Z
  have h2 : 2 < Fintype.card Z := by
    have := Nat.card_eq_fintype_card (α := Z)
    omega
  obtain ⟨a, b, c, hab', hac, hbc⟩ := Fintype.two_lt_card_iff.1 h2
  have key : ∀ x y : Z, x ≠ 1 → y ≠ 1 → x ≠ y → ∃ t c : PSL2Model f, t * t = 1 ∧ c * c = 1 ∧
      t * c = c * t ∧ t ≠ 1 ∧ c ≠ 1 ∧ t ≠ c := by
    intro x y hx hy hxy
    refine ⟨((x : Q) : PSL2Model f), ((y : Q) : PSL2Model f), hsq x, hsq y, hcomm x y, ?_, ?_, ?_⟩
    · intro h
      exact hx (Subtype.ext (Subtype.ext h))
    · intro h
      exact hy (Subtype.ext (Subtype.ext h))
    · intro h
      exact hxy (Subtype.ext (Subtype.ext h))
  by_cases ha1 : a = 1
  · exact key b c (fun h => hab' (ha1.trans h.symm)) (fun h => hac (ha1.trans h.symm)) hbc
  · by_cases hb1 : b = 1
    · exact key a c ha1 (fun h => hbc (hb1.trans h.symm)) hac
    · exact key a b ha1 hb1 hab'

section Products

variable (a b : PSL2Model f) {i j : Fin m}

theorem swp_mul_swp_right : (swp a i j * swp b i j).right = 1 := by
  rw [SemidirectProduct.mul_right, swp_right, swp_right, swap_mul_self]

theorem swp_mul_swp_left_fst (hij : i ≠ j) : (swp a i j * swp b i j).left i = a * b⁻¹ := by
  rw [WreathClass.mul_left_apply, swp_right, swap_inv, swap_apply_left, swp_left_fst hij,
    swp_left_snd hij]

theorem swp_mul_swp_left_snd (hij : i ≠ j) : (swp a i j * swp b i j).left j = a⁻¹ * b := by
  rw [WreathClass.mul_left_apply, swp_right, swap_inv, swap_apply_right, swp_left_snd hij,
    swp_left_fst hij]

theorem swp_mul_swp_left_of_ne {l : Fin m} (hli : l ≠ i) (hlj : l ≠ j) :
    (swp a i j * swp b i j).left l = 1 := by
  rw [WreathClass.mul_left_apply, swp_left_of_ne hli hlj, swp_right, swap_inv,
    swap_apply_of_ne_of_ne hli hlj, swp_left_of_ne hli hlj, one_mul]

variable (c : PSL2Model f)

theorem swp_mul_swp_mul_swp_left_fst (hij : i ≠ j) :
    (swp a i j * swp b i j * swp c i j).left i = a * b⁻¹ * c := by
  rw [WreathClass.mul_left_apply, swp_mul_swp_right, swp_mul_swp_left_fst a b hij, inv_one,
    Perm.one_apply, swp_left_fst hij]

theorem swp_mul_swp_mul_swp_left_snd (hij : i ≠ j) :
    (swp a i j * swp b i j * swp c i j).left j = a⁻¹ * b * c⁻¹ := by
  rw [WreathClass.mul_left_apply, swp_mul_swp_right, swp_mul_swp_left_snd a b hij, inv_one,
    Perm.one_apply, swp_left_snd hij]

theorem swp_mul_swp_mul_swp_left_of_ne {l : Fin m} (hli : l ≠ i) (hlj : l ≠ j) :
    (swp a i j * swp b i j * swp c i j).left l = 1 := by
  rw [WreathClass.mul_left_apply, swp_mul_swp_right, swp_mul_swp_left_of_ne a b hli hlj, inv_one,
    Perm.one_apply, swp_left_of_ne hli hlj, one_mul]

theorem swp_mul_swp_mul_swp_eq_one (hij : i ≠ j) (h1 : a * b⁻¹ * c = 1) (h2 : a⁻¹ * b * c⁻¹ = 1) :
    swp a i j * swp b i j * swp c i j = swp 1 i j := by
  refine SemidirectProduct.ext (funext fun l => ?_) ?_
  · by_cases hli : l = i
    · rw [hli, swp_mul_swp_mul_swp_left_fst a b c hij, swp_left_fst hij, h1]
    · by_cases hlj : l = j
      · rw [hlj, swp_mul_swp_mul_swp_left_snd a b c hij, swp_left_snd hij, h2, inv_one]
      · rw [swp_mul_swp_mul_swp_left_of_ne a b c hli hlj, swp_left_of_ne hli hlj]
  · rw [SemidirectProduct.mul_right, swp_mul_swp_right, swp_right, swp_right, one_mul]

theorem commute_swp_swp (hij : i ≠ j) (h1 : a * b⁻¹ = b * a⁻¹) (h2 : a⁻¹ * b = b⁻¹ * a) :
    Commute (swp a i j) (swp b i j) := by
  show swp a i j * swp b i j = swp b i j * swp a i j
  refine SemidirectProduct.ext (funext fun l => ?_) (by rw [swp_mul_swp_right, swp_mul_swp_right])
  by_cases hli : l = i
  · rw [hli, swp_mul_swp_left_fst a b hij, swp_mul_swp_left_fst b a hij, h1]
  · by_cases hlj : l = j
    · rw [hlj, swp_mul_swp_left_snd a b hij, swp_mul_swp_left_snd b a hij, h2]
    · rw [swp_mul_swp_left_of_ne a b hli hlj, swp_mul_swp_left_of_ne b a hli hlj]

theorem commute_swp_swp_iff (hij : i ≠ j) :
    Commute (swp a i j) (swp b i j) ↔ a * b⁻¹ * (a * b⁻¹) = 1 := by
  constructor
  · intro h
    have h1 := congrArg (fun w : L2Wreath f m => w.left i) h.eq
    rw [swp_mul_swp_left_fst a b hij, swp_mul_swp_left_fst b a hij] at h1
    exact eq_inv_iff_mul_eq_one.mp (show a * b⁻¹ = (a * b⁻¹)⁻¹ by
      rw [mul_inv_rev, inv_inv]; exact h1)
  · intro h
    have h1 : a * b⁻¹ = b * a⁻¹ := by
      rw [eq_inv_iff_mul_eq_one.mpr h, mul_inv_rev, inv_inv]
    have h3 : a⁻¹ * b = b⁻¹ * a := by
      calc a⁻¹ * b = a⁻¹ * (b * a⁻¹) * a := by group
        _ = a⁻¹ * (a * b⁻¹) * a := by rw [← h1]
        _ = b⁻¹ * a := by group
    exact commute_swp_swp a b hij h1 h3

theorem swp_injective (hij : i ≠ j) (h : swp a i j = swp b i j) : a = b := by
  have h1 := congrArg (fun w : L2Wreath f m => w.left i) h
  simpa only [swp_left_fst hij] using h1

end Products

theorem klein_relations {X : Type*} [Group X] {t c : X} (ht : t * t = 1) (hc : c * c = 1)
    (htc : t * c = c * t) :
    t⁻¹ = t ∧ c⁻¹ = c ∧ (t * c)⁻¹ = t * c ∧ t * c * (t * c) = 1 ∧
      t * (t * c) = (t * c) * t ∧ c * (t * c) = (t * c) * c := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  refine ⟨hti, hci, by rw [mul_inv_rev, hti, hci, htc], ?_, ?_, ?_⟩
  · calc t * c * (t * c) = t * (c * t) * c := by group
      _ = t * (t * c) * c := by rw [htc]
      _ = (t * t) * (c * c) := by group
      _ = 1 := by rw [ht, hc, one_mul]
  · calc t * (t * c) = t * (c * t) := by rw [htc]
      _ = (t * c) * t := by group
  · calc c * (t * c) = (c * t) * c := by group
      _ = (t * c) * c := by rw [htc]

theorem exists_swap_triple (hf : 2 ≤ f) (hm : 2 ≤ m) :
    ∃ v x₁ x₂ x₃ : L2Wreath f m, v ∈ swapSet f m ∧ x₁ ∈ swapSet f m ∧ x₂ ∈ swapSet f m ∧
      x₃ ∈ swapSet f m ∧ x₁ * x₂ * x₃ = v ∧
      Commute v x₁ ∧ Commute v x₂ ∧ Commute v x₃ ∧
      Commute x₁ x₂ ∧ Commute x₁ x₃ ∧ Commute x₂ x₃ ∧
      v ≠ x₁ ∧ v ≠ x₂ ∧ v ≠ x₃ ∧ x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ := by
  obtain ⟨t, c, ht, hc, htc, ht1, hc1, htc'⟩ := exists_klein_psl2 hf
  set i : Fin m := ⟨0, by omega⟩ with hi
  set j : Fin m := ⟨1, by omega⟩ with hj
  have hij : i ≠ j := by simp [hi, hj, Fin.ext_iff]
  obtain ⟨hti, hci, htci, htcsq, htct, hctc⟩ := klein_relations ht hc htc
  refine ⟨swp 1 i j, swp t i j, swp c i j, swp (t * c) i j, swp_mem hij, swp_mem hij,
    swp_mem hij, swp_mem hij, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine swp_mul_swp_mul_swp_eq_one t c (t * c) hij ?_ ?_
    · rw [hci]
      exact htcsq
    · rw [hti, htci]
      exact htcsq
  · refine commute_swp_swp _ _ hij ?_ ?_ <;> simp [hti]
  · refine commute_swp_swp _ _ hij ?_ ?_ <;> simp [hci]
  · refine commute_swp_swp _ _ hij ?_ ?_ <;> simp [htci]
  · refine commute_swp_swp _ _ hij ?_ ?_
    · rw [hci, hti, htc]
    · rw [hci, hti, htc]
  · refine commute_swp_swp _ _ hij ?_ ?_
    · rw [htci, hti]
      exact htct
    · rw [htci, hti]
      exact htct
  · refine commute_swp_swp _ _ hij ?_ ?_
    · rw [htci, hci]
      exact hctc
    · rw [htci, hci]
      exact hctc
  · exact fun h => ht1 (swp_injective _ _ hij h).symm
  · exact fun h => hc1 (swp_injective _ _ hij h).symm
  · intro h
    have h1 : t * c = 1 := (swp_injective _ _ hij h).symm
    exact htc' (by rw [eq_inv_of_mul_eq_one_right h1, hti])
  · exact fun h => htc' (swp_injective _ _ hij h)
  · intro h
    have h1 : t = t * c := swp_injective _ _ hij h
    exact hc1 (mul_left_cancel (a := t) (by rw [mul_one]; exact h1)).symm
  · intro h
    have h1 : c = t * c := swp_injective _ _ hij h
    exact ht1 (mul_right_cancel (b := c) (by rw [one_mul]; exact h1)).symm

end SwapKlein

end CFSG.OddTranspositions.PartThree

end

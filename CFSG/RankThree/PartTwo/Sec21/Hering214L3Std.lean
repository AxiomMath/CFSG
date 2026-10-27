module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119Sub

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.RankThree.PartTwo.Sec21.Hering2119
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits diagUnits_mul)
open CFSG.Assembly (IsElemAbelian)

section Klein

variable {H : Type*} [Group H]

theorem klein_closure {a b : H} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    ∀ w ∈ Subgroup.closure ({a, b} : Set H), w = 1 ∨ w = a ∨ w = b ∨ w = a * b := by
  have ha' : ∀ x : H, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hb' : ∀ x : H, b * (b * x) = x := fun x => by rw [← mul_assoc, hb, one_mul]
  have hba : b * a = a * b := hab.symm
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact Or.inr (Or.inl rfl)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp [ha]
    · simp
    · simp [ha', mul_assoc]
    · simp
    · simp [hba]
    · simp [hb]
    · exact Or.inr (Or.inl (by rw [hab, hb']))
    · simp
    · simp [mul_assoc, ha, hba, hb', ha']
    · simp [mul_assoc, hb, hba, ha']
    · refine Or.inl ?_
      calc a * b * (a * b) = a * (b * a) * b := by simp [mul_assoc]
        _ = a * (a * b) * b := by rw [hba]
        _ = 1 := by simp [mul_assoc, hb, ha']
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_left ha))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_left hb)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      apply inv_eq_of_mul_eq_one_left
      calc a * b * (a * b) = a * (b * a) * b := by simp [mul_assoc]
        _ = a * (a * b) * b := by rw [hba]
        _ = 1 := by simp [mul_assoc, hb, ha']

theorem mul_self_eq_one_of_mem_closure_pair {a b : H} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {w : H} (hw : w ∈ Subgroup.closure ({a, b} : Set H)) : w * w = 1 := by
  have hba : b * a = a * b := hab.symm
  rcases klein_closure ha hb hab w hw with rfl | rfl | rfl | rfl
  · simp
  · exact ha
  · exact hb
  · calc a * b * (a * b) = a * (b * a) * b := by simp [mul_assoc]
      _ = a * (a * b) * b := by rw [hba]
      _ = 1 := by
        rw [← mul_assoc, ha, one_mul, hb]

theorem isElemAbelian_closure_pair {a b : H} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : IsElemAbelian 2 (Subgroup.closure ({a, b} : Set H)) := by
  have hsq := fun {w : H} (hw : w ∈ Subgroup.closure ({a, b} : Set H)) =>
    mul_self_eq_one_of_mem_closure_pair ha hb hab hw
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have h1 := hsq (Subgroup.mul_mem _ x.2 y.2)
    have h2 := hsq x.2
    have h3 := hsq y.2
    have hxy : (x : H) * y = (y : H)⁻¹ * (x : H)⁻¹ := by
      have : (x : H) * y = ((x : H) * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      rw [this, _root_.mul_inv_rev]
    have hxi : (x : H)⁻¹ = x := inv_eq_of_mul_eq_one_left h2
    have hyi : (y : H)⁻¹ = y := inv_eq_of_mul_eq_one_left h3
    show (x : H) * y = y * x
    rw [hxy, hxi, hyi]
  · rw [pow_two]
    exact hsq hx

theorem card_closure_pair {a b : H} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card (Subgroup.closure ({a, b} : Set H)) = 4 := by
  have hset : ((Subgroup.closure ({a, b} : Set H) : Subgroup H) : Set H) = {1, a, b, a * b} := by
    ext w
    constructor
    · intro hw
      rcases klein_closure ha hb hab w hw with rfl | rfl | rfl | rfl <;> simp
    · intro hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hne
    have h' : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h']
    exact (inv_eq_of_mul_eq_one_left ha).symm
  have hab_a : a * b ≠ a := by
    intro h
    apply hb1
    simpa using h
  have hab_b : a * b ≠ b := by
    intro h
    apply ha1
    simpa using h
  have hcard : Nat.card (Subgroup.closure ({a, b} : Set H)) =
      Set.ncard ({1, a, b, a * b} : Set H) := by
    rw [← hset, ← Nat.card_coe_set_eq]
    rfl
  rw [hcard]
  have h1 : (1 : H) ∉ ({a, b, a * b} : Set H) := by
    simp [Ne.symm ha1, Ne.symm hb1, Ne.symm hab1]
  have h2 : a ∉ ({b, a * b} : Set H) := by
    simp [hne, Ne.symm hab_a]
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
    Set.ncard_pair (Ne.symm hab_b)]

end Klein

section Std

variable {F : Type} [Field F]

theorem xHom_eq_one_iff (t : F) : xHom F (Multiplicative.ofAdd t) = 1 ↔ t = 0 := by
  constructor
  · intro h
    rw [xHom_ofAdd, LinearFlag.proj_eq_one_iff, LinearFlag.mem_scalars] at h
    obtain ⟨c, -, hc⟩ := h
    have h01 := congrFun (congrFun hc 0) 1
    simpa [coe_xSL, Matrix.scalar_apply, Matrix.diagonal_apply] using h01
  · rintro rfl
    rw [xHom_ofAdd, xSL_zero, map_one]

theorem xHom_injective : Function.Injective (xHom F) := by
  intro x y hxy
  have h : xHom F (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hx : x * y⁻¹ = Multiplicative.ofAdd (Multiplicative.toAdd (x * y⁻¹)) := rfl
  rw [hx, xHom_eq_one_iff] at h
  rw [toAdd_mul, toAdd_inv, add_neg_eq_zero] at h
  exact Multiplicative.toAdd.injective h

theorem sq_add_add_one_eq_zero' {τ : F} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    τ ^ 2 + τ + 1 = 0 := by
  have h : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by
    have : (τ - 1) * (τ ^ 2 + τ + 1) = τ ^ 3 - 1 := by ring
    rw [this, hτ3, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hτ1
  · exact h

theorem sq_eq_one_add [CharP F 2] {τ : F} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) : τ ^ 2 = 1 + τ := by
  have h := sq_add_add_one_eq_zero' hτ3 hτ1
  have h' : τ ^ 2 = -(τ + 1) := by linear_combination h
  rw [h', CharTwo.neg_eq, add_comm]

theorem eq_one_or_eq_or_eq_sq {τ s : F} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (hs : s ^ 3 = 1) :
    s = 1 ∨ s = τ ∨ s = τ ^ 2 := by
  have h := sq_add_add_one_eq_zero' hτ3 hτ1
  have hsum : 1 + τ + τ ^ 2 = 0 := by linear_combination h
  have hsum2 : τ + τ ^ 2 + 1 = 0 := by linear_combination h
  have hprod : (s - 1) * ((s - τ) * (s - τ ^ 2)) = 0 := by
    have : (s - 1) * ((s - τ) * (s - τ ^ 2)) =
        s ^ 3 - (1 + τ + τ ^ 2) * s ^ 2 + (τ + τ ^ 2 + τ ^ 3) * s - τ ^ 3 := by ring
    rw [this, hs, hτ3, hsum]
    have h3 : τ + τ ^ 2 + 1 = 0 := hsum2
    rw [h3]
    ring
  rcases mul_eq_zero.mp hprod with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · rcases mul_eq_zero.mp h2 with h2 | h3
    · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h3))

theorem mul_mem_cubes {τ u v : F} (hτ3 : τ ^ 3 = 1) (hu : u = 1 ∨ u = τ ∨ u = τ ^ 2)
    (hv : v = 1 ∨ v = τ ∨ v = τ ^ 2) : u * v = 1 ∨ u * v = τ ∨ u * v = τ ^ 2 := by
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · left; ring
  · right; left; ring
  · right; right; ring
  · right; left; ring
  · right; right; ring
  · left; linear_combination hτ3
  · right; right; ring
  · left; linear_combination hτ3
  · right; left; linear_combination τ * hτ3

theorem exists_std_four [CharP F 2] {τ : Fˣ} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    ∃ W : Subgroup (projectiveSL 3 F), IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      (∀ s t : Fˣ, s ^ 3 = 1 → t ^ 3 = 1 → ∀ w ∈ W, conjAut 3 F (diagUnits 1 s t) w ∈ W) ∧
      ∃ w ∈ W, conjAut 3 F (diagUnits 1 τ 1) w ≠ w := by
  set a : projectiveSL 3 F := xHom F (Multiplicative.ofAdd (1 : F)) with ha_def
  set b : projectiveSL 3 F := xHom F (Multiplicative.ofAdd (τ : F)) with hb_def
  have hτF3 : (τ : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hτ3, Units.val_one]
  have hτF1 : (τ : F) ≠ 1 := fun h => hτ1 (Units.ext h)
  have hτ0 : (τ : F) ≠ 0 := τ.ne_zero
  have hsq : (τ : F) ^ 2 = 1 + τ := sq_eq_one_add hτF3 hτF1
  have hτinv : (τ : F)⁻¹ = (τ : F) ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hτF3)
  have hτ2inv : ((τ : F) ^ 2)⁻¹ = (τ : F) :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ]; exact hτF3)
  have hmul : ∀ u v : F, xHom F (Multiplicative.ofAdd u) * xHom F (Multiplicative.ofAdd v) =
      xHom F (Multiplicative.ofAdd (u + v)) := by
    intro u v
    rw [← map_mul, ofAdd_add]
  have haa : a * a = 1 := by
    rw [ha_def, hmul, CharTwo.add_self_eq_zero, ofAdd_zero, map_one]
  have hbb : b * b = 1 := by
    rw [hb_def, hmul, CharTwo.add_self_eq_zero, ofAdd_zero, map_one]
  have hab : a * b = b * a := by
    rw [ha_def, hb_def, hmul, hmul, add_comm]
  have ha1 : a ≠ 1 := fun h => one_ne_zero ((xHom_eq_one_iff (1 : F)).mp h)
  have hb1 : b ≠ 1 := fun h => hτ0 ((xHom_eq_one_iff (τ : F)).mp h)
  have hne : a ≠ b := fun h =>
    hτF1 (Multiplicative.ofAdd.injective (xHom_injective h)).symm
  set W : Subgroup (projectiveSL 3 F) := Subgroup.closure ({a, b} : Set (projectiveSL 3 F))
    with hW
  have haW : a ∈ W := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbW : b ∈ W := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hmemW : ∀ u : F, (u = 1 ∨ u = τ ∨ u = (τ : F) ^ 2) →
      xHom F (Multiplicative.ofAdd u) ∈ W := by
    rintro u (rfl | rfl | rfl)
    · exact haW
    · exact hbW
    · rw [hsq]
      have : xHom F (Multiplicative.ofAdd (1 + (τ : F))) = a * b := (hmul 1 τ).symm
      rw [this]
      exact W.mul_mem haW hbW
  refine ⟨W, isElemAbelian_closure_pair haa hbb hab,
    card_closure_pair haa hbb hab ha1 hb1 hne, ?_, a, haW, ?_⟩
  · intro s t hs ht w hw
    have hsF : (s : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hs, Units.val_one]
    have hsinv : ((s : F)⁻¹ = 1 ∨ (s : F)⁻¹ = τ ∨ (s : F)⁻¹ = (τ : F) ^ 2) := by
      rcases eq_one_or_eq_or_eq_sq hτF3 hτF1 hsF with h | h | h
      · left; rw [h, inv_one]
      · right; right; rw [h, hτinv]
      · right; left; rw [h, hτ2inv]
    have hφ : ∀ u : F, (u = 1 ∨ u = τ ∨ u = (τ : F) ^ 2) →
        conjAut 3 F (diagUnits 1 s t) (xHom F (Multiplicative.ofAdd u)) ∈ W := by
      intro u hu
      rw [conjAut_diagUnits_xHom]
      apply hmemW
      simp only [Units.val_one, one_mul]
      exact mul_mem_cubes hτF3 hsinv hu
    have hmap : W.map (conjAut 3 F (diagUnits 1 s t)).toMonoidHom ≤ W := by
      rw [hW, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with rfl | hx
      · exact hφ 1 (Or.inl rfl)
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hφ τ (Or.inr (Or.inl rfl))
    exact hmap ⟨w, hw, rfl⟩
  · rw [ha_def, conjAut_diagUnits_xHom]
    intro h
    have h' := Multiplicative.ofAdd.injective (xHom_injective h)
    simp only [Units.val_one, one_mul, mul_one, hτinv] at h'
    apply hτF1
    have h3 : (τ : F) ^ 3 = (τ : F) * (τ : F) ^ 2 := by ring
    rw [h', mul_one] at h3
    rw [← hτF3, h3]

end Std

end CFSG.RankThree.PartTwo.Sec21.Hering214

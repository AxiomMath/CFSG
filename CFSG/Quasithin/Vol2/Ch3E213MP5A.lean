module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.Quasithin.Ch3E213M.P5

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {k : Type} [Field k]

@[expose] def uu (a b c : k) : Matrix.SpecialLinearGroup (Fin 3) k :=
  ⟨!![1, a, c; 0, 1, b; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_uu (a b c : k) :
    ((uu a b c : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      !![1, a, c; 0, 1, b; 0, 0, 1] := rfl

theorem uu_mul (a b c a' b' c' : k) :
    uu a b c * uu a' b' c' = uu (a + a') (b + b') (c + c' + a * b') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uu, coe_uu, coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uu_zero : uu (0 : k) 0 0 = 1 := by
  apply Subtype.ext
  rw [coe_uu, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem uu_inv (a b c : k) : (uu a b c)⁻¹ = uu (-a) (-b) (a * b - c) := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [uu_mul, ← uu_zero]
  congr 1 <;> ring

theorem uu_injective {a b c a' b' c' : k} (h : uu a b c = uu a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h' := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k)) h
  simp only [coe_uu] at h'
  exact ⟨congrFun (congrFun h' 0) 1, congrFun (congrFun h' 1) 2, congrFun (congrFun h' 0) 2⟩

theorem uu_eq_one_iff {a b c : k} : uu a b c = 1 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    rw [← uu_zero] at h
    exact uu_injective h
  · rintro ⟨rfl, rfl, rfl⟩
    exact uu_zero

theorem uu_mem_unitriangular (a b c : k) : uu a b c ∈ unitriangular 3 k := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [coe_uu, Fin.lt_def]
  · fin_cases i <;> simp [coe_uu]

theorem exists_eq_uu {g : Matrix.SpecialLinearGroup (Fin 3) k} (hg : g ∈ unitriangular 3 k) :
    ∃ a b c : k, g = uu a b c := by
  obtain ⟨hlow, hdiag⟩ := hg
  refine ⟨(g : Matrix (Fin 3) (Fin 3) k) 0 1, (g : Matrix (Fin 3) (Fin 3) k) 1 2,
    (g : Matrix (Fin 3) (Fin 3) k) 0 2, Subtype.ext ?_⟩
  rw [coe_uu]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hdiag, hlow 1 0 (by decide), hlow 2 0 (by decide), hlow 2 1 (by decide)]

theorem uu_mul_self [CharP k 2] (a b c : k) : uu a b c * uu a b c = uu 0 0 (a * b) := by
  rw [uu_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
    zero_add]

variable (k) in
@[expose] def ua1 : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k) where
  carrier := {g | ∃ a c : k, g = uu a 0 c}
  one_mem' := ⟨0, 0, uu_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, c, rfl⟩ ⟨a', c', rfl⟩
    exact ⟨a + a', c + c' + a * 0, by rw [uu_mul, add_zero]⟩
  inv_mem' := by
    rintro _ ⟨a, c, rfl⟩
    exact ⟨-a, a * 0 - c, by rw [uu_inv, neg_zero]⟩

variable (k) in
@[expose] def ua2 : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k) where
  carrier := {g | ∃ b c : k, g = uu 0 b c}
  one_mem' := ⟨0, 0, uu_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨b, c, rfl⟩ ⟨b', c', rfl⟩
    exact ⟨b + b', c + c' + 0 * b', by rw [uu_mul, add_zero]⟩
  inv_mem' := by
    rintro _ ⟨b, c, rfl⟩
    exact ⟨-b, 0 * b - c, by rw [uu_inv, neg_zero]⟩

variable (k) in
@[expose] def uzz : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k) where
  carrier := {g | ∃ c : k, g = uu 0 0 c}
  one_mem' := ⟨0, uu_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
    exact ⟨c + c' + 0 * 0, by rw [uu_mul, add_zero]⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    exact ⟨0 * 0 - c, by rw [uu_inv, neg_zero]⟩

theorem mem_ua1 {g : Matrix.SpecialLinearGroup (Fin 3) k} : g ∈ ua1 k ↔ ∃ a c : k, g = uu a 0 c :=
  Iff.rfl

theorem mem_uzz {g : Matrix.SpecialLinearGroup (Fin 3) k} : g ∈ uzz k ↔ ∃ c : k, g = uu 0 0 c :=
  Iff.rfl

theorem ua1_le_unitriangular : ua1 k ≤ unitriangular 3 k := by
  rintro _ ⟨a, c, rfl⟩
  exact uu_mem_unitriangular a 0 c

theorem ua2_le_unitriangular : ua2 k ≤ unitriangular 3 k := by
  rintro _ ⟨b, c, rfl⟩
  exact uu_mem_unitriangular 0 b c

theorem ua1_inf_ua2 : ua1 k ⊓ ua2 k = uzz k := by
  ext g
  constructor
  · rintro ⟨⟨a, c, rfl⟩, ⟨b', c', h⟩⟩
    obtain ⟨ha, -, -⟩ := uu_injective h
    exact ⟨c, by rw [ha]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨⟨0, c, rfl⟩, ⟨0, c, rfl⟩⟩

theorem le_or_le_of_mul_self [CharP k 2] {W : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k)}
    (hW : W ≤ unitriangular 3 k) (h2 : ∀ x ∈ W, x * x = 1) : W ≤ ua1 k ∨ W ≤ ua2 k := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2'⟩ := h
  obtain ⟨w₁, hw₁, hw₁'⟩ := Set.not_subset.mp h1
  obtain ⟨w₂, hw₂, hw₂'⟩ := Set.not_subset.mp h2'
  obtain ⟨a, b, c, rfl⟩ := exists_eq_uu (hW hw₁)
  obtain ⟨a', b', c', rfl⟩ := exists_eq_uu (hW hw₂)
  have hb : b ≠ 0 := fun hb => hw₁' ⟨a, c, by rw [hb]⟩
  have ha' : a' ≠ 0 := fun ha => hw₂' ⟨b', c', by rw [ha]⟩
  have hab : a * b = 0 := by
    have := h2 _ hw₁
    rw [uu_mul_self, uu_eq_one_iff] at this
    exact this.2.2
  have hab' : a' * b' = 0 := by
    have := h2 _ hw₂
    rw [uu_mul_self, uu_eq_one_iff] at this
    exact this.2.2
  have ha : a = 0 := (mul_eq_zero.mp hab).resolve_right hb
  have hb' : b' = 0 := (mul_eq_zero.mp hab').resolve_left ha'
  have h3 := h2 _ (W.mul_mem hw₁ hw₂)
  rw [uu_mul, uu_mul_self, uu_eq_one_iff, ha, hb', zero_add, add_zero] at h3
  exact mul_ne_zero ha' hb h3.2.2

end CFSG.Quasithin.Ch3E213M.P5

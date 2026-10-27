module

public import CFSG.Quasithin.Vol2.Ch3E213MSp4G41

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat minorJ minorJ_apply minorJ_mul_self minorJ_transpose antiUnipotent
    mem_antiUnipotent_iff_upper mem_antiSp transpose_mul_minorJ_mul_apply)

variable {k : Type} [Field k]

@[expose] def IsUpper (g : antiSp k) : Prop :=
  ∀ i j : Fin 4, j < i → glMat (g : GL (Fin 4) k) i j = 0

theorem upper_mul_apply_of_lt {A B : Matrix (Fin 4) (Fin 4) k}
    (hA : ∀ i j : Fin 4, j < i → A i j = 0) (hB : ∀ i j : Fin 4, j < i → B i j = 0)
    {i j : Fin 4} (hij : j < i) : (A * B) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge l i with h | h
  · rw [hA i l h, zero_mul]
  · rw [hB l j (lt_of_lt_of_le hij h), mul_zero]

theorem upper_mul_apply_self {A B : Matrix (Fin 4) (Fin 4) k}
    (hA : ∀ i j : Fin 4, j < i → A i j = 0) (hB : ∀ i j : Fin 4, j < i → B i j = 0)
    (i : Fin 4) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hA i l h, zero_mul]
    · rw [hB l i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem isUpper_mul {g h : antiSp k} (hg : IsUpper g) (hh : IsUpper h) : IsUpper (g * h) :=
  fun _ _ hij => upper_mul_apply_of_lt (A := glMat (g : GL (Fin 4) k))
    (B := glMat (h : GL (Fin 4) k)) hg hh hij

theorem isUpper_inv {g : antiSp k} (hg : IsUpper g) : IsUpper g⁻¹ := by
  intro i j hij
  rw [glMat_inv_eq]
  fin_cases i <;> fin_cases j <;> simp at hij <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply] <;> exact hg _ _ (by decide)

theorem isUpper_diag_mul_inv {g : antiSp k} (hg : IsUpper g) (i : Fin 4) :
    glMat (g : GL (Fin 4) k) i i * glMat ((g⁻¹ : antiSp k) : GL (Fin 4) k) i i = 1 := by
  have h1 : glMat (g : GL (Fin 4) k) * glMat ((g⁻¹ : antiSp k) : GL (Fin 4) k) = 1 :=
    (g : GL (Fin 4) k).mul_inv
  rw [← upper_mul_apply_self hg (isUpper_inv hg) i, h1, Matrix.one_apply_eq]

theorem isUpper_diag_ne_zero {g : antiSp k} (hg : IsUpper g) (i : Fin 4) :
    glMat (g : GL (Fin 4) k) i i ≠ 0 :=
  left_ne_zero_of_mul_eq_one (isUpper_diag_mul_inv hg i)

theorem isUpper_of_flag {g : antiSp k} (h10 : glMat (g : GL (Fin 4) k) 1 0 = 0)
    (h20 : glMat (g : GL (Fin 4) k) 2 0 = 0) (h30 : glMat (g : GL (Fin 4) k) 3 0 = 0)
    (h21 : glMat (g : GL (Fin 4) k) 2 1 = 0) (h31 : glMat (g : GL (Fin 4) k) 3 1 = 0) :
    IsUpper g := by
  have hJ := mem_antiSp.mp g.2
  have e02 := congrFun (congrFun hJ 0) 2
  have e03 := congrFun (congrFun hJ 0) 3
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at e02 e03
  rw [h10, h20, h30] at e02 e03
  norm_num at e02 e03
  have h32 : glMat (g : GL (Fin 4) k) 3 2 = 0 := by
    rcases e02 with h | h
    · rw [h, zero_mul] at e03
      exact absurd e03 zero_ne_one
    · exact h
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption

section CharTwo

variable [CharP k 2]

theorem mem_normalizer_of_isUpper {g : antiSp k} (hg : IsUpper g) :
    g ∈ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) := by
  have key : ∀ c : antiSp k, IsUpper c → ∀ u ∈ antiUnipotent k, c * u * c⁻¹ ∈ antiUnipotent k := by
    intro c hc u hu
    obtain ⟨huU, hu1⟩ := (mem_antiUnipotent_iff_upper u).mp hu
    have hcu := isUpper_mul hc huU
    refine (mem_antiUnipotent_iff_upper _).mpr ⟨isUpper_mul hcu (isUpper_inv hc), fun i => ?_⟩
    change (glMat ((c * u : antiSp k) : GL (Fin 4) k) *
      glMat ((c⁻¹ : antiSp k) : GL (Fin 4) k)) i i = 1
    rw [upper_mul_apply_self hcu (isUpper_inv hc)]
    change (glMat (c : GL (Fin 4) k) * glMat (u : GL (Fin 4) k)) i i * _ = 1
    rw [upper_mul_apply_self hc huU, hu1, mul_one, isUpper_diag_mul_inv hc]
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨key g hg u, fun h => ?_⟩
  have := key g⁻¹ (isUpper_inv hg) _ h
  rwa [inv_inv, show g⁻¹ * (g * u * g⁻¹) * g = u by group] at this

end CharTwo

@[expose] def wLong : antiSp k :=
  ⟨⟨minorJ k, minorJ k, minorJ_mul_self, minorJ_mul_self⟩, by
    rw [mem_antiSp]
    change (minorJ k).transpose * minorJ k * minorJ k = minorJ k
    rw [minorJ_transpose, minorJ_mul_self, Matrix.one_mul]⟩

theorem glMat_wLong : glMat ((wLong : antiSp k) : GL (Fin 4) k) = minorJ k :=
  rfl

theorem isOppStd_conj_of_isUpper {c : antiSp k} (hc : IsUpper c) :
    IsOppStd (c * wLong * c⁻¹) := by
  have hci := isUpper_inv hc
  set A := glMat (c : GL (Fin 4) k) with hA
  set B := glMat ((c⁻¹ : antiSp k) : GL (Fin 4) k) with hB
  have hM : glMat ((c * wLong * c⁻¹ : antiSp k) : GL (Fin 4) k) = A * minorJ k * B := rfl
  have entry : ∀ i j : Fin 4, (A * minorJ k * B) i j =
      A i 0 * B 3 j + A i 1 * B 2 j + A i 2 * B 1 j + A i 3 * B 0 j := by
    intro i j
    simp [Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply]
    ring
  have hd0 := isUpper_diag_ne_zero hci 0
  have hd1 := isUpper_diag_ne_zero hci 1
  have hd2 := isUpper_diag_ne_zero hc 2
  have hd3 := isUpper_diag_ne_zero hc 3
  rw [← hB] at hd0 hd1
  rw [← hA] at hd2 hd3
  have a30 : A 3 0 = 0 := hc 3 0 (by decide)
  have a31 : A 3 1 = 0 := hc 3 1 (by decide)
  have a32 : A 3 2 = 0 := hc 3 2 (by decide)
  have a20 : A 2 0 = 0 := hc 2 0 (by decide)
  have a21 : A 2 1 = 0 := hc 2 1 (by decide)
  have b10 : B 1 0 = 0 := hci 1 0 (by decide)
  have b20 : B 2 0 = 0 := hci 2 0 (by decide)
  have b30 : B 3 0 = 0 := hci 3 0 (by decide)
  have b21 : B 2 1 = 0 := hci 2 1 (by decide)
  have b31 : B 3 1 = 0 := hci 3 1 (by decide)
  refine ⟨?_, ?_⟩
  · rw [hM, entry, a30, a31, a32]
    simpa using mul_ne_zero hd3 hd0
  · rw [hM, entry, entry, entry, entry, a30, a31, a32, a20, a21, b10, b20, b30, b21, b31]
    have : A 2 3 * B 0 0 * (A 3 3 * B 0 1) -
        (A 2 2 * B 1 1 + A 2 3 * B 0 1) * (A 3 3 * B 0 0) = -(A 2 2 * B 1 1 * (A 3 3 * B 0 0)) :=
      by ring
    simp only [zero_mul, mul_zero, zero_add, add_zero]
    rw [this, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero hd2 hd1) (mul_ne_zero hd3 hd0)

end CFSG.Quasithin.Ch3E213M

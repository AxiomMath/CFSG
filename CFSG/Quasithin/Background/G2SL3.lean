module

public import CFSG.Quasithin.Background.G2SL2
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

public section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups commutatorElement

namespace CFSG.Quasithin.SL3Model

open CFSG.Quasithin.SL2Model

variable {F : Type*} [Field F]

abbrev W3 (F : Type*) [Field F] : Type _ := Multiplicative (Fin 3 → F)

@[expose] def natAct3 : SL(3, F) →* MulAut (W3 F) where
  toFun A :=
    { toFun := fun w => Multiplicative.ofAdd (A • Multiplicative.toAdd w)
      invFun := fun w => Multiplicative.ofAdd (A⁻¹ • Multiplicative.toAdd w)
      left_inv := fun w => by simp
      right_inv := fun w => by simp
      map_mul' := fun a b => by simp [smul_add] }
  map_one' := by
    ext w
    simp
  map_mul' := fun A B => by
    ext w
    simp [mul_smul]

theorem natAct3_apply (A : SL(3, F)) (w : W3 F) :
    natAct3 A w = Multiplicative.ofAdd (A • Multiplicative.toAdd w) := rfl

theorem smul_single_one (A : SL(3, F)) (j i : Fin 3) :
    (A • (Pi.single j 1 : Fin 3 → F)) i = A.1 i j := by
  change (A.1 *ᵥ (Pi.single j 1 : Fin 3 → F)) i = _
  simp

theorem natAct3_injective : Function.Injective (natAct3 : SL(3, F) →* MulAut (W3 F)) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have := congrArg (fun ρ : MulAut (W3 F) =>
    Multiplicative.toAdd (ρ (Multiplicative.ofAdd (Pi.single j 1))) i) h
  simpa [natAct3_apply, smul_single_one] using this

abbrev vE (F : Type*) [Field F] (i : Fin 3) : Fin 3 → F := Pi.single i 1

@[expose] def Qv (v : Fin 3 → F) : Subgroup SL(3, F) where
  carrier := {A | A • v = v ∧ ∀ x, ∃ c : F, A • x = x + c • v}
  one_mem' := ⟨one_smul _ _, fun x => ⟨0, by simp⟩⟩
  mul_mem' := by
    rintro A B ⟨hAv, hA⟩ ⟨hBv, hB⟩
    refine ⟨by rw [mul_smul, hBv, hAv], fun x => ?_⟩
    obtain ⟨c, hc⟩ := hB x
    obtain ⟨c', hc'⟩ := hA x
    refine ⟨c + c', ?_⟩
    rw [mul_smul, hc, smul_add, smul_comm A c v, hAv, hc', add_smul]
    abel
  inv_mem' := by
    rintro A ⟨hAv, hA⟩
    refine ⟨by rw [inv_smul_eq_iff, hAv], fun x => ?_⟩
    obtain ⟨c, hc⟩ := hA (A⁻¹ • x)
    refine ⟨-c, ?_⟩
    rw [smul_inv_smul] at hc
    rw [neg_smul, ← sub_eq_add_neg]
    exact eq_sub_of_add_eq hc.symm

theorem mem_Qv {v : Fin 3 → F} {A : SL(3, F)} :
    A ∈ Qv v ↔ A • v = v ∧ ∀ x, ∃ c : F, A • x = x + c • v := Iff.rfl

theorem mem_Qv_conj {v : Fin 3 → F} (γ A : SL(3, F)) :
    γ * A * γ⁻¹ ∈ Qv (γ • v) ↔ A ∈ Qv v := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun x => ?_⟩
    · have : γ • (A • v) = γ • v := by
        rw [← mul_smul]
        simpa [mul_smul] using h1
      exact MulAction.injective γ this
    · obtain ⟨c, hc⟩ := h2 (γ • x)
      refine ⟨c, ?_⟩
      have : γ • (A • x) = γ • (x + c • v) := by
        rw [smul_add, smul_comm γ c v]
        simpa [mul_smul] using hc
      exact MulAction.injective γ this
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun x => ?_⟩
    · simp [mul_smul, h1]
    · obtain ⟨c, hc⟩ := h2 (γ⁻¹ • x)
      refine ⟨c, ?_⟩
      simp [mul_smul, hc, smul_add, smul_comm γ c v]

theorem transvection_smul {i j : Fin 3} (hij : i ≠ j) (a : F) (x : Fin 3 → F) :
    transvection hij a • x = x + (a * x j) • (Pi.single i 1 : Fin 3 → F) := by
  change ((transvection hij a).1 *ᵥ x) = _
  rw [transvection_coe]
  ext k
  by_cases hk : k = i
  · subst hk
    simp [Matrix.add_mulVec, Matrix.single_mulVec]
  · simp [Matrix.add_mulVec, Matrix.single_mulVec, hk]

theorem transvection_mem_Qv {i j : Fin 3} (hij : i ≠ j) (a : F) :
    transvection hij a ∈ Qv (vE F i) := by
  refine ⟨?_, fun x => ⟨a * x j, transvection_smul hij a x⟩⟩
  rw [transvection_smul]
  simp [hij.symm]

theorem diag2n_decompose_01 (a : F) (ha : a ≠ 0) :
    diag2n (show (0 : Fin 3) ≠ 1 by decide) a ha =
      transvection (show (0 : Fin 3) ≠ 1 by decide) a *
      transvection (show (1 : Fin 3) ≠ 0 by decide) (-a⁻¹) *
      transvection (show (0 : Fin 3) ≠ 1 by decide) a *
      transvection (show (0 : Fin 3) ≠ 1 by decide) (-1) *
      transvection (show (1 : Fin 3) ≠ 0 by decide) 1 *
      transvection (show (0 : Fin 3) ≠ 1 by decide) (-1) := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      mul_add, add_mul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

theorem diag2n_decompose_02 (a : F) (ha : a ≠ 0) :
    diag2n (show (0 : Fin 3) ≠ 2 by decide) a ha =
      transvection (show (0 : Fin 3) ≠ 2 by decide) a *
      transvection (show (2 : Fin 3) ≠ 0 by decide) (-a⁻¹) *
      transvection (show (0 : Fin 3) ≠ 2 by decide) a *
      transvection (show (0 : Fin 3) ≠ 2 by decide) (-1) *
      transvection (show (2 : Fin 3) ≠ 0 by decide) 1 *
      transvection (show (0 : Fin 3) ≠ 2 by decide) (-1) := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      mul_add, add_mul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

theorem diag2n_decompose_10 (a : F) (ha : a ≠ 0) :
    diag2n (show (1 : Fin 3) ≠ 0 by decide) a ha =
      transvection (show (1 : Fin 3) ≠ 0 by decide) a *
      transvection (show (0 : Fin 3) ≠ 1 by decide) (-a⁻¹) *
      transvection (show (1 : Fin 3) ≠ 0 by decide) a *
      transvection (show (1 : Fin 3) ≠ 0 by decide) (-1) *
      transvection (show (0 : Fin 3) ≠ 1 by decide) 1 *
      transvection (show (1 : Fin 3) ≠ 0 by decide) (-1) := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      mul_add, add_mul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

theorem diag2n_decompose_12 (a : F) (ha : a ≠ 0) :
    diag2n (show (1 : Fin 3) ≠ 2 by decide) a ha =
      transvection (show (1 : Fin 3) ≠ 2 by decide) a *
      transvection (show (2 : Fin 3) ≠ 1 by decide) (-a⁻¹) *
      transvection (show (1 : Fin 3) ≠ 2 by decide) a *
      transvection (show (1 : Fin 3) ≠ 2 by decide) (-1) *
      transvection (show (2 : Fin 3) ≠ 1 by decide) 1 *
      transvection (show (1 : Fin 3) ≠ 2 by decide) (-1) := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      mul_add, add_mul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

theorem diag2n_decompose_20 (a : F) (ha : a ≠ 0) :
    diag2n (show (2 : Fin 3) ≠ 0 by decide) a ha =
      transvection (show (2 : Fin 3) ≠ 0 by decide) a *
      transvection (show (0 : Fin 3) ≠ 2 by decide) (-a⁻¹) *
      transvection (show (2 : Fin 3) ≠ 0 by decide) a *
      transvection (show (2 : Fin 3) ≠ 0 by decide) (-1) *
      transvection (show (0 : Fin 3) ≠ 2 by decide) 1 *
      transvection (show (2 : Fin 3) ≠ 0 by decide) (-1) := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      mul_add, add_mul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

theorem diag2n_decompose_21 (a : F) (ha : a ≠ 0) :
    diag2n (show (2 : Fin 3) ≠ 1 by decide) a ha =
      transvection (show (2 : Fin 3) ≠ 1 by decide) a *
      transvection (show (1 : Fin 3) ≠ 2 by decide) (-a⁻¹) *
      transvection (show (2 : Fin 3) ≠ 1 by decide) a *
      transvection (show (2 : Fin 3) ≠ 1 by decide) (-1) *
      transvection (show (1 : Fin 3) ≠ 2 by decide) 1 *
      transvection (show (2 : Fin 3) ≠ 1 by decide) (-1) := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [diag2n_coe, transvection_coe, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      mul_add, add_mul, mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

theorem diag2n_mem {J : Subgroup SL(3, F)}
    (ht : ∀ (i j : Fin 3) (hij : i ≠ j) (a : F), transvection hij a ∈ J)
    (i j : Fin 3) (hij : i ≠ j) (a : F) (ha : a ≠ 0) : diag2n hij a ha ∈ J := by
  have six : ∀ {i j : Fin 3} (hij : i ≠ j) (a : F),
      transvection hij a * transvection hij.symm (-a⁻¹) * transvection hij a *
        transvection hij (-1) * transvection hij.symm 1 * transvection hij (-1) ∈ J :=
    fun hij a => J.mul_mem (J.mul_mem (J.mul_mem (J.mul_mem (J.mul_mem (ht _ _ _ _) (ht _ _ _ _))
      (ht _ _ _ _)) (ht _ _ _ _)) (ht _ _ _ _)) (ht _ _ _ _)
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · rw [diag2n_decompose_01 a ha]
    exact six _ a
  · rw [diag2n_decompose_02 a ha]
    exact six _ a
  · rw [diag2n_decompose_10 a ha]
    exact six _ a
  · exact absurd rfl hij
  · rw [diag2n_decompose_12 a ha]
    exact six _ a
  · rw [diag2n_decompose_20 a ha]
    exact six _ a
  · rw [diag2n_decompose_21 a ha]
    exact six _ a
  · exact absurd rfl hij

theorem Qv_gen : Qv (vE F 0) ⊔ Qv (vE F 1) ⊔ Qv (vE F 2) = ⊤ := by
  set J : Subgroup SL(3, F) := Qv (vE F 0) ⊔ Qv (vE F 1) ⊔ Qv (vE F 2) with hJ
  have ht : ∀ (i j : Fin 3) (hij : i ≠ j) (a : F), transvection hij a ∈ J := by
    intro i j hij a
    have h := transvection_mem_Qv hij a
    fin_cases i
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left h)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right h)
    · exact Subgroup.mem_sup_right h
  refine eq_top_iff.2 fun A _ => ?_
  exact diagonal_transvection_induction' (fun A => A ∈ J) A
    (fun i j hij c hc => diag2n_mem ht i j hij c hc) ht (fun A B hA hB => J.mul_mem hA hB)

@[expose] def tq (b c : F) : SL(3, F) :=
  ⟨!![1, b, c; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem tq_coe (b c : F) :
    (tq b c : Matrix (Fin 3) (Fin 3) F) = !![1, b, c; 0, 1, 0; 0, 0, 1] := rfl

theorem tq_smul (b c : F) (x : Fin 3 → F) :
    tq b c • x = ![x 0 + b * x 1 + c * x 2, x 1, x 2] := by
  change ((tq b c).1 *ᵥ x) = _
  ext i
  fin_cases i <;> simp [tq_coe, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem tq_add (b c b' c' : F) : tq (b + b') (c + c') = tq b c * tq b' c' := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tq_coe, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem tq_zero : tq (0 : F) 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tq_coe]

theorem tq_injective {b c b' c' : F} (h : tq b c = tq b' c') : b = b' ∧ c = c' := by
  have h1 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 0 1) h
  have h2 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 0 2) h
  simp [tq_coe] at h1 h2
  exact ⟨h1, h2⟩

theorem tq_mem_Qv (b c : F) : tq b c ∈ Qv (vE F 0) := by
  refine ⟨?_, fun x => ⟨b * x 1 + c * x 2, ?_⟩⟩
  · rw [tq_smul]
    ext i
    fin_cases i <;> simp
  · rw [tq_smul]
    ext i
    fin_cases i <;> simp [add_assoc]

theorem mem_Qv_e0 {A : SL(3, F)} : A ∈ Qv (vE F 0) ↔ ∃ b c : F, tq b c = A := by
  constructor
  · rintro ⟨h0, h⟩
    obtain ⟨c₁, hc₁⟩ := h (vE F 1)
    obtain ⟨c₂, hc₂⟩ := h (vE F 2)
    refine ⟨c₁, c₂, ?_⟩
    apply Subtype.ext
    ext i j
    have e0 := fun i => smul_single_one A 0 i
    have e1 := fun i => smul_single_one A 1 i
    have e2 := fun i => smul_single_one A 2 i
    rw [h0] at e0
    rw [hc₁] at e1
    rw [hc₂] at e2
    fin_cases i <;> fin_cases j
    · simpa [tq_coe] using (e0 0)
    · simpa [tq_coe] using (e1 0)
    · simpa [tq_coe] using (e2 0)
    · simpa [tq_coe] using (e0 1)
    · simpa [tq_coe] using (e1 1)
    · simpa [tq_coe] using (e2 1)
    · simpa [tq_coe] using (e0 2)
    · simpa [tq_coe] using (e1 2)
    · simpa [tq_coe] using (e2 2)
  · rintro ⟨b, c, rfl⟩
    exact tq_mem_Qv b c

@[expose] def qhom : Wm F →* SL(3, F) where
  toFun q := tq (Multiplicative.toAdd q 1) (Multiplicative.toAdd q 0)
  map_one' := tq_zero
  map_mul' a b := by simp [← tq_add]

theorem qhom_apply (q : Wm F) :
    qhom q = tq (Multiplicative.toAdd q 1) (Multiplicative.toAdd q 0) := rfl

theorem qhom_injective : Function.Injective (qhom : Wm F →* SL(3, F)) := by
  intro a b h
  obtain ⟨h1, h0⟩ := tq_injective h
  apply Multiplicative.toAdd.injective
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem qhom_range : (qhom : Wm F →* SL(3, F)).range = Qv (vE F 0) := by
  ext A
  rw [mem_Qv_e0]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨_, _, rfl⟩
  · rintro ⟨b, c, rfl⟩
    exact ⟨Multiplicative.ofAdd ![c, b], by simp [qhom_apply]⟩

theorem card_Qv : Nat.card (Qv (vE F 0)) = Nat.card F ^ 2 := by
  have h1 : Nat.card (Wm F) = Nat.card F ^ 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
    simp
  rw [← qhom_range, ← h1]
  exact (Nat.card_congr (MonoidHom.ofInjective qhom_injective).toEquiv).symm

theorem Qv_comm [CharP F 2] (A B : SL(3, F)) (hA : A ∈ Qv (vE F 0)) (hB : B ∈ Qv (vE F 0)) :
    A * B = B * A := by
  obtain ⟨b, c, rfl⟩ := mem_Qv_e0.1 hA
  obtain ⟨b', c', rfl⟩ := mem_Qv_e0.1 hB
  rw [← tq_add, ← tq_add, add_comm b, add_comm c]

theorem Qv_sq [CharP F 2] (A : SL(3, F)) (hA : A ∈ Qv (vE F 0)) : A * A = 1 := by
  obtain ⟨b, c, rfl⟩ := mem_Qv_e0.1 hA
  rw [← tq_add, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, tq_zero]

@[expose] def blkMat (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, M 0 0, M 0 1; 0, M 1 0, M 1 1]

theorem blkMat_mul (M N : Matrix (Fin 2) (Fin 2) F) : blkMat (M * N) = blkMat M * blkMat N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem det_blkMat (M : Matrix (Fin 2) (Fin 2) F) : (blkMat M).det = M.det := by
  simp [blkMat, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] def blk : SL(2, F) →* SL(3, F) where
  toFun M := ⟨blkMat M.1, by rw [det_blkMat, M.2]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blkMat]
  map_mul' M N := Subtype.ext (blkMat_mul M.1 N.1)

theorem blk_coe (M : SL(2, F)) :
    (blk M : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, M.1 0 0, M.1 0 1; 0, M.1 1 0, M.1 1 1] := rfl

theorem blk_mul_tq [CharP F 2] (M : SL(2, F)) (b c : F) :
    blk M * tq b c = tq ((M • ![c, b]) 1) ((M • ![c, b]) 0) * blk M := by
  have hdet := det_eq_one' M
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, blk_coe, tq_coe, Matrix.mul_apply, Fin.sum_univ_three,
      smul_vec]
  · linear_combination (-b) * hdet + (-(b * M.1 0 1 * M.1 1 0) - M.1 0 0 * M.1 1 0 * c) * h2
  · linear_combination (-c) * hdet + (-(c * M.1 0 1 * M.1 1 0) - M.1 0 1 * M.1 1 1 * b) * h2

theorem blk_conj_tq [CharP F 2] (M : SL(2, F)) (b c : F) :
    blk M * tq b c * (blk M)⁻¹ = tq ((M • ![c, b]) 1) ((M • ![c, b]) 0) := by
  rw [mul_inv_eq_iff_eq_mul]
  exact blk_mul_tq M b c

theorem blk_qhom [CharP F 2] (M : SL(2, F)) (q : Wm F) :
    blk M * qhom q * (blk M)⁻¹ = qhom (natAct M q) := by
  have hq : ![Multiplicative.toAdd q 0, Multiplicative.toAdd q 1] = Multiplicative.toAdd q := by
    ext i; fin_cases i <;> simp
  rw [qhom_apply, blk_conj_tq, qhom_apply, natAct_apply, toAdd_ofAdd, hq]

theorem Qv_irreducible [Finite F] [CharP F 2] (X : Subgroup SL(3, F)) (hXQ : X ≤ Qv (vE F 0))
    (hX : ∀ M ∈ commutator SL(2, F), ∀ x ∈ X, blk M * x * (blk M)⁻¹ ∈ X) :
    X = ⊥ ∨ X = Qv (vE F 0) := by
  let X' : Subgroup (Wm F) := X.comap qhom
  have hX' : ∀ A ∈ commutator SL(2, F), ∀ x ∈ X', natAct A x ∈ X' := by
    intro A hA x hx
    show qhom (natAct A x) ∈ X
    rw [← blk_qhom]
    exact hX A hA _ hx
  have key : ∀ b c : F, tq b c = qhom (Multiplicative.ofAdd ![c, b]) := fun b c => by
    simp [qhom_apply]
  rcases natAct_irreducible_comm X' hX' with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨b, c, rfl⟩ := mem_Qv_e0.1 (hXQ hx)
    have hmem : (Multiplicative.ofAdd ![c, b] : Wm F) ∈ X' := by
      show qhom _ ∈ X
      rw [← key]
      exact hx
    rw [h, Subgroup.mem_bot] at hmem
    have h0 := congrFun (Multiplicative.ofAdd.injective hmem) 0
    have h1 := congrFun (Multiplicative.ofAdd.injective hmem) 1
    simp at h0 h1
    rw [Subgroup.mem_bot, h0, h1, tq_zero]
  · right
    apply le_antisymm hXQ
    intro x hx
    obtain ⟨b, c, rfl⟩ := mem_Qv_e0.1 hx
    have hmem : (Multiplicative.ofAdd ![c, b] : Wm F) ∈ X' := by rw [h]; exact Subgroup.mem_top _
    have : qhom (Multiplicative.ofAdd ![c, b]) ∈ X := hmem
    rwa [← key] at this

@[expose] def Pt (v : Fin 3 → F) : Subgroup SL(3, F) where
  carrier := {A | ∃ c : F, A • v = c • v}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro A B ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by rw [mul_smul, hb, smul_comm A b v, ha, smul_smul, mul_comm]⟩
  inv_mem' := by
    rintro A ⟨a, ha⟩
    by_cases hv : v = 0
    · exact ⟨0, by simp [hv]⟩
    · have ha0 : a ≠ 0 := by
        rintro rfl
        apply hv
        have : A • v = 0 := by rw [ha]; simp
        have h2 := congrArg (fun x => A⁻¹ • x) this
        simpa using h2
      refine ⟨a⁻¹, ?_⟩
      rw [inv_smul_eq_iff, smul_comm A a⁻¹ v, ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]

theorem mem_Pt {v : Fin 3 → F} {A : SL(3, F)} : A ∈ Pt v ↔ ∃ c : F, A • v = c • v := Iff.rfl

theorem Qv_le_Pt (v : Fin 3 → F) : Qv v ≤ Pt v := fun A hA => ⟨1, by rw [hA.1, one_smul]⟩

theorem mem_Pt_e0 {A : SL(3, F)} : A ∈ Pt (vE F 0) ↔ A.1 1 0 = 0 ∧ A.1 2 0 = 0 := by
  constructor
  · rintro ⟨c, hc⟩
    have h1 := smul_single_one A 0 1
    have h2 := smul_single_one A 0 2
    rw [hc] at h1 h2
    simp at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨h1, h2⟩
    refine ⟨A.1 0 0, ?_⟩
    ext i
    have := smul_single_one A 0 i
    rw [this]
    fin_cases i <;> simp [h1, h2]

@[expose] def lv (A : SL(3, F)) (y : Fin 2 → F) : Fin 2 → F :=
  ![A.1 1 1 * y 0 + A.1 1 2 * y 1, A.1 2 1 * y 0 + A.1 2 2 * y 1]

theorem lv_mul {A : SL(3, F)} (hA : A ∈ Pt (vE F 0)) (B : SL(3, F)) (y : Fin 2 → F) :
    lv (A * B) y = lv A (lv B y) := by
  obtain ⟨h1, h2⟩ := mem_Pt_e0.1 hA
  ext i
  fin_cases i <;>
    simp [lv, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, h1, h2] <;>
    ring

theorem lv_one (y : Fin 2 → F) : lv (1 : SL(3, F)) y = y := by
  ext i
  fin_cases i <;> simp [lv]

theorem lv_add (A : SL(3, F)) (y y' : Fin 2 → F) : lv A (y + y') = lv A y + lv A y' := by
  ext i
  fin_cases i <;> simp [lv] <;> ring

@[expose] def levi : Pt (vE F 0) →* MulAut (Wm F) where
  toFun A :=
    { toFun := fun w => Multiplicative.ofAdd (lv A.1 (Multiplicative.toAdd w))
      invFun := fun w => Multiplicative.ofAdd (lv (A⁻¹).1 (Multiplicative.toAdd w))
      left_inv := fun w => by
        simp only [toAdd_ofAdd]
        rw [← lv_mul (A⁻¹).2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, lv_one,
          ofAdd_toAdd]
      right_inv := fun w => by
        simp only [toAdd_ofAdd]
        rw [← lv_mul A.2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, lv_one,
          ofAdd_toAdd]
      map_mul' := fun a b => by simp [lv_add] }
  map_one' := by
    ext w
    simp [lv_one]
  map_mul' A B := by
    ext w
    simp [lv_mul A.2]

theorem levi_apply (A : Pt (vE F 0)) (w : Wm F) :
    levi A w = Multiplicative.ofAdd (lv A.1 (Multiplicative.toAdd w)) := rfl

theorem blk_mem_Pt (M : SL(2, F)) : blk M ∈ Pt (vE F 0) := by
  rw [mem_Pt_e0]
  simp [blk_coe]

theorem levi_blk (M : SL(2, F)) : levi ⟨blk M, blk_mem_Pt M⟩ = natAct M := by
  ext w i
  rw [levi_apply, natAct_apply]
  simp only [toAdd_ofAdd]
  fin_cases i <;> simp [lv, blk_coe, smul_eq_mulVec', Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem normal_two_le_Qv [Finite F] [CharP F 2] (N : Subgroup SL(3, F))
    (hNP : N ≤ Pt (vE F 0))
    (hN : ∀ p ∈ Pt (vE F 0), ∀ x ∈ N, p * x * p⁻¹ ∈ N) (hp : IsPGroup 2 N) :
    N ≤ Qv (vE F 0) := by
  classical
  let N' : Subgroup (Pt (vE F 0)) := N.subgroupOf (Pt (vE F 0))
  have hp' : IsPGroup 2 N' := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNP).symm
  let ρ : N' →* MulAut (Wm F) := levi.comp N'.subtype
  let _inst : MulAction N' (Wm F) := MulAction.compHom (Wm F) ρ
  have _hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hp'.card_modEq_card_fixedPoints (Wm F)
  have hcard : Nat.card (Wm F) = Nat.card F ^ 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
    simp
  have heven : Even (Nat.card (Wm F)) := by
    rw [hcard]
    exact (card_F_even (F := F)).pow_of_ne_zero (by norm_num)
  have hfix : ∃ w : Wm F, w ≠ 1 ∧ ∀ n : N', levi n.1 w = w := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ w ∈ MulAction.fixedPoints N' (Wm F), w = 1 := by
      intro w hw
      by_contra hne
      obtain ⟨n, hn⟩ := hcon w hne
      exact hn (hw n)
    have h1 : Nat.card ↥(MulAction.fixedPoints N' (Wm F)) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      exact ⟨⟨1, fun n => map_one (levi n.1)⟩, fun ⟨w, hw⟩ => Subtype.ext (hsub w hw)⟩
    rw [h1] at hmod
    obtain ⟨k, hk⟩ := heven
    rw [hk] at hmod
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨w₀, hw₀1, hw₀⟩ := hfix
  let C : Subgroup (Wm F) :=
    { carrier := {w | ∀ n : N', levi n.1 w = w}
      one_mem' := fun n => map_one _
      mul_mem' := fun {a b} ha hb n => by rw [map_mul, ha n, hb n]
      inv_mem' := fun {a} ha n => by rw [map_inv, ha n] }
  have hC : ∀ A : SL(2, F), ∀ x ∈ C, natAct A x ∈ C := by
    intro A x hx n
    have hn : (n.1 : SL(3, F)) ∈ N := n.2
    have hn' : (blk A)⁻¹ * (n.1 : SL(3, F)) * blk A ∈ N := by
      have := hN ((blk A)⁻¹) (inv_mem (blk_mem_Pt A)) _ hn
      simpa using this
    let n' : N' := ⟨⟨(blk A)⁻¹ * (n.1 : SL(3, F)) * blk A, hNP hn'⟩, hn'⟩
    have hcomm : n.1 * (⟨blk A, blk_mem_Pt A⟩ : Pt (vE F 0)) = ⟨blk A, blk_mem_Pt A⟩ * n'.1 := by
      apply Subtype.ext
      show (n.1 : SL(3, F)) * blk A = blk A * ((blk A)⁻¹ * (n.1 : SL(3, F)) * blk A)
      group
    rw [← levi_blk A]
    show levi n.1 (levi ⟨blk A, blk_mem_Pt A⟩ x) = levi ⟨blk A, blk_mem_Pt A⟩ x
    rw [← MulAut.mul_apply, ← map_mul, hcomm, map_mul, MulAut.mul_apply, hx n']
  have hCtop : C = ⊤ := by
    rcases natAct_irreducible_comm C (fun A _ x hx => hC A x hx) with h | h
    · have hw : w₀ ∈ C := hw₀
      rw [h, Subgroup.mem_bot] at hw
      exact absurd hw hw₀1
    · exact h
  intro n hn
  have hnP := hNP hn
  obtain ⟨h10, h20⟩ := mem_Pt_e0.1 hnP
  have hfixall : ∀ w : Wm F, levi ⟨n, hnP⟩ w = w := fun w => by
    have : w ∈ C := by rw [hCtop]; exact Subgroup.mem_top w
    exact this ⟨⟨n, hnP⟩, hn⟩
  have hA := hfixall (Multiplicative.ofAdd ![1, 0])
  have hB := hfixall (Multiplicative.ofAdd ![0, 1])
  rw [levi_apply] at hA hB
  have hA' := congrArg Multiplicative.toAdd hA
  have hB' := congrArg Multiplicative.toAdd hB
  simp only [toAdd_ofAdd] at hA' hB'
  have h11 : n.1 1 1 = 1 := by simpa [lv] using congrFun hA' 0
  have h21 : n.1 2 1 = 0 := by simpa [lv] using congrFun hA' 1
  have h12 : n.1 1 2 = 0 := by simpa [lv] using congrFun hB' 0
  have h22 : n.1 2 2 = 1 := by simpa [lv] using congrFun hB' 1
  have hdet := n.2
  rw [Matrix.det_fin_three] at hdet
  have h00 : n.1 0 0 = 1 := by
    simpa [h10, h20, h11, h21, h12, h22] using hdet
  refine mem_Qv_e0.2 ⟨n.1 0 1, n.1 0 2, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tq_coe, h00, h10, h20, h11, h21, h12, h22]

@[expose] def ext2 : Wm F →* W3 F where
  toFun w := Multiplicative.ofAdd ![Multiplicative.toAdd w 0, Multiplicative.toAdd w 1, 0]
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp

@[expose] def proj2 : W3 F →* Wm F where
  toFun w := Multiplicative.ofAdd ![Multiplicative.toAdd w 0, Multiplicative.toAdd w 1]
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp

theorem proj2_ext2 (w : Wm F) : proj2 (ext2 w) = w := by
  apply Multiplicative.toAdd.injective
  ext i
  fin_cases i <;> simp [proj2, ext2]

@[expose] def Triv (ρ : MulAut (W3 F)) : Prop :=
  ∀ w : W3 F, Multiplicative.toAdd (ρ w) 1 = Multiplicative.toAdd w 1 ∧
    Multiplicative.toAdd (ρ w) 2 = Multiplicative.toAdd w 2

theorem Triv.symm {ρ : MulAut (W3 F)} (h : Triv ρ) : Triv ρ.symm := fun w => by
  have := h (ρ.symm w)
  rw [MulEquiv.apply_symm_apply] at this
  exact ⟨this.1.symm, this.2.symm⟩

theorem Triv.ext2_eq {ρ : MulAut (W3 F)} (h : Triv ρ) (w : Wm F) :
    ρ (ext2 w) = ext2 (proj2 (ρ (ext2 w))) := by
  apply Multiplicative.toAdd.injective
  have h2 := (h (ext2 w)).2
  ext i
  fin_cases i
  · simp [proj2, ext2]
  · simp [proj2, ext2]
  · simpa [proj2, ext2] using h2

theorem Triv.one : Triv (1 : MulAut (W3 F)) := fun _ => ⟨rfl, rfl⟩

theorem Triv.mul {ρ σ : MulAut (W3 F)} (hρ : Triv ρ) (hσ : Triv σ) : Triv (ρ * σ) := fun w => by
  rw [MulAut.mul_apply]
  exact ⟨(hρ (σ w)).1.trans (hσ w).1, (hρ (σ w)).2.trans (hσ w).2⟩

theorem Triv.pow {ρ : MulAut (W3 F)} (h : Triv ρ) (m : ℕ) : Triv (ρ ^ m) := by
  induction m with
  | zero => simpa using Triv.one
  | succ m ih => rw [pow_succ]; exact ih.mul h

@[expose] def restr2 (ρ : MulAut (W3 F)) (h : Triv ρ) : MulAut (Wm F) where
  toFun w := proj2 (ρ (ext2 w))
  invFun w := proj2 (ρ.symm (ext2 w))
  left_inv w := by
    show proj2 (ρ.symm (ext2 (proj2 (ρ (ext2 w))))) = w
    rw [← h.ext2_eq, MulEquiv.symm_apply_apply, proj2_ext2]
  right_inv w := by
    show proj2 (ρ (ext2 (proj2 (ρ.symm (ext2 w))))) = w
    rw [← h.symm.ext2_eq, MulEquiv.apply_symm_apply, proj2_ext2]
  map_mul' a b := by simp [map_mul]

theorem restr2_apply (ρ : MulAut (W3 F)) (h : Triv ρ) (w : Wm F) :
    restr2 ρ h w = proj2 (ρ (ext2 w)) := rfl

theorem apply_ext2 (ρ : MulAut (W3 F)) (h : Triv ρ) (w : Wm F) :
    ρ (ext2 w) = ext2 (restr2 ρ h w) := h.ext2_eq w

theorem restr2_pow (ρ : MulAut (W3 F)) (h : Triv ρ) (m : ℕ) (w : Wm F) :
    (restr2 ρ h ^ m) w = proj2 ((ρ ^ m) (ext2 w)) := by
  induction m with
  | zero => simp [proj2_ext2]
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply, ih, restr2_apply, ← (h.pow m).ext2_eq, pow_succ',
      MulAut.mul_apply]

theorem smul_coord (A : SL(3, F)) (x : Fin 3 → F) (i : Fin 3) :
    (A • x) i = A.1 i 0 * x 0 + A.1 i 1 * x 1 + A.1 i 2 * x 2 := by
  change (A.1 *ᵥ x) i = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem natAct3_coord (A : SL(3, F)) (v : W3 F) (i : Fin 3) :
    Multiplicative.toAdd (natAct3 A v) i = A.1 i 0 * Multiplicative.toAdd v 0 +
      A.1 i 1 * Multiplicative.toAdd v 1 + A.1 i 2 * Multiplicative.toAdd v 2 := by
  rw [natAct3_apply, toAdd_ofAdd, smul_coord]

@[expose] def blk2Mat (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1]

theorem blk2Mat_mul (M N : Matrix (Fin 2) (Fin 2) F) : blk2Mat (M * N) = blk2Mat M * blk2Mat N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2Mat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem det_blk2Mat (M : Matrix (Fin 2) (Fin 2) F) : (blk2Mat M).det = M.det := by
  simp [blk2Mat, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] def blk2 : SL(2, F) →* SL(3, F) where
  toFun M := ⟨blk2Mat M.1, by rw [det_blk2Mat, M.2]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk2Mat]
  map_mul' M N := Subtype.ext (blk2Mat_mul M.1 N.1)

theorem blk2_coe (M : SL(2, F)) :
    (blk2 M : Matrix (Fin 3) (Fin 3) F) =
      !![M.1 0 0, M.1 0 1, 0; M.1 1 0, M.1 1 1, 0; 0, 0, 1] := rfl

theorem blk2_ext2 (M : SL(2, F)) (w : Wm F) : natAct3 (blk2 M) (ext2 w) = ext2 (natAct M w) := by
  apply Multiplicative.toAdd.injective
  ext i
  rw [natAct3_coord]
  fin_cases i <;>
    simp [blk2_coe, ext2, natAct_apply, smul_eq_mulVec']

@[expose] def eW (F : Type*) [Field F] (i : Fin 3) : W3 F := Multiplicative.ofAdd (Pi.single i 1)

theorem toAdd_eW (i j : Fin 3) : Multiplicative.toAdd (eW F i) j = (Pi.single i 1 : Fin 3 → F) j := rfl

theorem natAct_coord2 (B : SL(2, F)) (v : Wm F) (i : Fin 2) :
    Multiplicative.toAdd (natAct B v) i =
      B.1 i 0 * Multiplicative.toAdd v 0 + B.1 i 1 * Multiplicative.toAdd v 1 := by
  rw [natAct_apply, toAdd_ofAdd]
  change (B.1 *ᵥ Multiplicative.toAdd v) i = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem plane_hb (ρ : MulAut (W3 F)) (hT : Triv ρ)
    (hb : ∀ A : SL(3, F), ∃ A' : SL(3, F), ∀ w : W3 F, ρ (natAct3 A w) = natAct3 A' (ρ w))
    (A : SL(2, F)) :
    ∃ B : SL(2, F), ∀ w : Wm F, restr2 ρ hT (natAct A w) = natAct B (restr2 ρ hT w) := by
  obtain ⟨A', hA'⟩ := hb (blk2 A)
  have h0 : Multiplicative.toAdd (ρ (eW F 0)) 1 = 0 ∧ Multiplicative.toAdd (ρ (eW F 0)) 2 = 0 := by
    have := hT (eW F 0)
    simpa [toAdd_eW] using this
  have h1 : Multiplicative.toAdd (ρ (eW F 1)) 1 = 1 ∧ Multiplicative.toAdd (ρ (eW F 1)) 2 = 0 := by
    have := hT (eW F 1)
    simpa [toAdd_eW] using this
  have h2 : Multiplicative.toAdd (ρ (eW F 2)) 1 = 0 ∧ Multiplicative.toAdd (ρ (eW F 2)) 2 = 1 := by
    have := hT (eW F 2)
    simpa [toAdd_eW] using this
  have hs : Multiplicative.toAdd (ρ (eW F 0)) 0 ≠ 0 := by
    intro hs
    have : ρ (eW F 0) = 1 := by
      apply Multiplicative.toAdd.injective
      ext i
      fin_cases i
      · simpa using hs
      · simpa using h0.1
      · simpa using h0.2
    have := ρ.injective (this.trans (map_one ρ).symm)
    have h3 := congrArg (fun v : W3 F => Multiplicative.toAdd v 0) this
    simp [toAdd_eW] at h3
  have e20 : A'.1 2 0 = 0 := by
    have h := congrArg (fun v : W3 F => Multiplicative.toAdd v 2) (hA' (eW F 0))
    rw [(hT _).2, natAct3_coord, natAct3_coord] at h
    simp [blk2_coe, toAdd_eW, h0.1, h0.2] at h
    exact h.resolve_right hs
  have e21 : A'.1 2 1 = 0 := by
    have h := congrArg (fun v : W3 F => Multiplicative.toAdd v 2) (hA' (eW F 1))
    rw [(hT _).2, natAct3_coord, natAct3_coord] at h
    simp [blk2_coe, toAdd_eW, h1.1, h1.2, e20] at h
    exact h.symm
  have e22 : A'.1 2 2 = 1 := by
    have hfix : natAct3 (blk2 A) (eW F 2) = eW F 2 := by
      apply Multiplicative.toAdd.injective
      ext i
      rw [natAct3_coord]
      fin_cases i <;> simp [blk2_coe, toAdd_eW]
    have h := congrArg (fun v : W3 F => Multiplicative.toAdd v 2) (hA' (eW F 2))
    rw [hfix, natAct3_coord] at h
    simp [h2.1, h2.2, e20] at h
    exact h.symm
  have hdet : A'.1 0 0 * A'.1 1 1 - A'.1 0 1 * A'.1 1 0 = 1 := by
    have h := A'.2
    rw [Matrix.det_fin_three] at h
    simp [e20, e21, e22] at h
    linear_combination h
  let B : SL(2, F) := ⟨!![A'.1 0 0, A'.1 0 1; A'.1 1 0, A'.1 1 1], by
    simp [Matrix.det_fin_two]; linear_combination hdet⟩
  refine ⟨B, fun w => ?_⟩
  have hv2 : Multiplicative.toAdd (ρ (ext2 w)) 2 = 0 := by
    have := (hT (ext2 w)).2
    simpa [ext2] using this
  apply Multiplicative.toAdd.injective
  ext i
  rw [restr2_apply, restr2_apply, ← blk2_ext2, hA']
  fin_cases i
  · show Multiplicative.toAdd (natAct3 A' (ρ (ext2 w))) 0 =
      Multiplicative.toAdd (natAct B (proj2 (ρ (ext2 w)))) 0
    rw [natAct3_coord, natAct_coord2]
    simp [B, proj2, hv2]
  · show Multiplicative.toAdd (natAct3 A' (ρ (ext2 w))) 1 =
      Multiplicative.toAdd (natAct B (proj2 (ρ (ext2 w)))) 1
    rw [natAct3_coord, natAct_coord2]
    simp [B, proj2, hv2]

theorem plane_lemma [CharP F 2] (ρ : MulAut (W3 F)) (hT : Triv ρ)
    (hb : ∀ A : SL(3, F), ∃ A' : SL(3, F), ∀ w : W3 F, ρ (natAct3 A w) = natAct3 A' (ρ w))
    (hc : ∃ k : ℕ, ρ ^ (2 ^ k) = 1) :
    ∃ b : F, ∀ w : Wm F, ρ (ext2 w) = ext2 (natAct (e12 b) w) := by
  obtain ⟨k, hk⟩ := hc
  have ha₂ : ∀ w : Wm F, Multiplicative.toAdd (restr2 ρ hT w) 1 = Multiplicative.toAdd w 1 := by
    intro w
    have := (hT (ext2 w)).1
    simpa [restr2_apply, proj2, ext2] using this
  have hc₂ : ∃ k : ℕ, restr2 ρ hT ^ (2 ^ k) = 1 := by
    refine ⟨k, ?_⟩
    ext w
    rw [restr2_pow, hk, MulAut.one_apply, proj2_ext2]
    rfl
  obtain ⟨b, hb'⟩ := normalizing_lemma (restr2 ρ hT) ha₂ (plane_hb ρ hT hb) hc₂
  refine ⟨b, fun w => ?_⟩
  rw [apply_ext2 ρ hT w, hb']

@[expose] def swapSL [CharP F 2] : SL(3, F) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by
    simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

theorem swapSL_mul_self [CharP F 2] : (swapSL : SL(3, F)) * swapSL = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapSL, Matrix.mul_apply, Fin.sum_univ_three]

theorem swapSL_coord [CharP F 2] (v : W3 F) :
    Multiplicative.toAdd (natAct3 (swapSL : SL(3, F)) v) 0 = Multiplicative.toAdd v 0 ∧
    Multiplicative.toAdd (natAct3 (swapSL : SL(3, F)) v) 1 = Multiplicative.toAdd v 2 ∧
    Multiplicative.toAdd (natAct3 (swapSL : SL(3, F)) v) 2 = Multiplicative.toAdd v 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [natAct3_coord] <;> simp [swapSL]

theorem normalizing_lemma3 [CharP F 2] (ρ : MulAut (W3 F)) (hT : Triv ρ)
    (hb : ∀ A : SL(3, F), ∃ A' : SL(3, F), ∀ w : W3 F, ρ (natAct3 A w) = natAct3 A' (ρ w))
    (hc : ∃ k : ℕ, ρ ^ (2 ^ k) = 1) :
    ∃ b c : F, ∀ w : W3 F, ρ w = natAct3 (tq b c) w := by
  obtain ⟨b, hb₁⟩ := plane_lemma ρ hT hb hc
  set a : MulAut (W3 F) := natAct3 (swapSL : SL(3, F)) with ha
  have haa : a * a = 1 := by rw [ha, ← map_mul, swapSL_mul_self, map_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  set ρ' : MulAut (W3 F) := a * ρ * a⁻¹ with hρ'
  have hρ'w : ∀ w, ρ' w = a (ρ (a w)) := fun w => by
    rw [hρ', hainv, MulAut.mul_apply, MulAut.mul_apply]
  have sc : ∀ v : W3 F, Multiplicative.toAdd (a v) 1 = Multiplicative.toAdd v 2 ∧
      Multiplicative.toAdd (a v) 2 = Multiplicative.toAdd v 1 := fun v =>
    ⟨(swapSL_coord v).2.1, (swapSL_coord v).2.2⟩
  have hT' : Triv ρ' := fun w => by
    rw [hρ'w]
    refine ⟨?_, ?_⟩
    · rw [(sc (ρ (a w))).1, (hT (a w)).2, (sc w).2]
    · rw [(sc (ρ (a w))).2, (hT (a w)).1, (sc w).1]
  have hbM : ∀ A : SL(3, F), ∃ A' : SL(3, F), ρ * natAct3 A = natAct3 A' * ρ := fun A => by
    obtain ⟨A', h⟩ := hb A
    exact ⟨A', MulEquiv.ext fun w => by simpa using h w⟩
  have hb' : ∀ A : SL(3, F), ∃ A' : SL(3, F),
      ∀ w : W3 F, ρ' (natAct3 A w) = natAct3 A' (ρ' w) := fun A => by
    obtain ⟨A₁', h⟩ := hbM ((swapSL : SL(3, F))⁻¹ * A * swapSL)
    refine ⟨swapSL * A₁' * (swapSL : SL(3, F))⁻¹, fun w => ?_⟩
    have hnA : natAct3 A = a * natAct3 ((swapSL : SL(3, F))⁻¹ * A * swapSL) * a⁻¹ := by
      simp [ha, map_mul, map_inv, mul_assoc]
    have hmain : ρ' * natAct3 A = natAct3 (swapSL * A₁' * (swapSL : SL(3, F))⁻¹) * ρ' := by
      calc ρ' * natAct3 A
          = a * (ρ * natAct3 ((swapSL : SL(3, F))⁻¹ * A * swapSL)) * a⁻¹ := by
            rw [hρ', hnA]; group
        _ = a * (natAct3 A₁' * ρ) * a⁻¹ := by rw [h]
        _ = natAct3 (swapSL * A₁' * (swapSL : SL(3, F))⁻¹) * ρ' := by
            rw [hρ']; simp [ha, map_mul, map_inv, mul_assoc]
    simpa using congrArg (fun σ : MulAut (W3 F) => σ w) hmain
  have hc' : ∃ k : ℕ, ρ' ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hc
    exact ⟨k, by rw [hρ', conj_pow, hk]; simp⟩
  obtain ⟨c, hc₁⟩ := plane_lemma ρ' hT' hb' hc'
  refine ⟨b, c, fun w => ?_⟩
  have hρ₁ : ∀ x y : F, Multiplicative.toAdd (ρ (Multiplicative.ofAdd ![x, y, 0])) =
      ![x + b * y, y, 0] := fun x y => by
    have := congrArg Multiplicative.toAdd (hb₁ (Multiplicative.ofAdd ![x, y]))
    simpa [ext2, natAct_apply, e12_smul, mul_comm] using this
  have haa' : ∀ x : W3 F, a (a x) = x := fun x => by
    simpa using congrArg (fun σ : MulAut (W3 F) => σ x) haa
  have key : ∀ u, ρ (a u) = a (ρ' u) := fun u => by
    rw [hρ'w u, haa']
  have hρ₂ : ∀ z : F, Multiplicative.toAdd (ρ (Multiplicative.ofAdd ![0, 0, z])) =
      ![c * z, 0, z] := fun z => by
    have hv : Multiplicative.toAdd (ext2 (natAct (e12 c) (Multiplicative.ofAdd ![0, z]))) =
        ![c * z, z, 0] := by
      simp [ext2, natAct_apply, e12_smul]
    have s := swapSL_coord (ext2 (natAct (e12 c) (Multiplicative.ofAdd ![0, z])))
    rw [hv] at s
    have hw : (Multiplicative.ofAdd ![0, 0, z] : W3 F) =
        a (ext2 (Multiplicative.ofAdd ![0, z])) := by
      apply Multiplicative.toAdd.injective
      ext i
      have s' := swapSL_coord (ext2 (Multiplicative.ofAdd ![0, z]) : W3 F)
      fin_cases i
      · exact s'.1.symm
      · exact s'.2.1.symm
      · exact s'.2.2.symm
    rw [hw, key, hc₁]
    ext i
    fin_cases i
    · exact s.1
    · exact s.2.1
    · exact s.2.2
  have hρ : ∀ x y z : F, Multiplicative.toAdd (ρ (Multiplicative.ofAdd ![x, y, z])) =
      ![x + b * y + c * z, y, z] := fun x y z => by
    have hsplit : (Multiplicative.ofAdd ![x, y, z] : W3 F) =
        Multiplicative.ofAdd ![x, y, 0] * Multiplicative.ofAdd ![0, 0, z] := by
      apply Multiplicative.toAdd.injective
      ext i
      fin_cases i <;> simp
    rw [hsplit, map_mul, toAdd_mul, hρ₁, hρ₂]
    ext i
    fin_cases i <;> simp
  apply Multiplicative.toAdd.injective
  have hw : w = Multiplicative.ofAdd ![Multiplicative.toAdd w 0, Multiplicative.toAdd w 1,
      Multiplicative.toAdd w 2] := by
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp
  rw [hw, hρ, natAct3_apply, toAdd_ofAdd, tq_smul]
  simp

theorem exists_smul_eq_e0_of_ne (w : Fin 3 → F) (hw : w 0 ≠ 0) :
    ∃ g : SL(3, F), g • w = Pi.single 0 1 := by
  refine ⟨⟨!![(w 0)⁻¹, 0, 0; -w 1, w 0, 0; -w 2 * (w 0)⁻¹, 0, 1], by
    simp [Matrix.det_fin_three, hw]⟩, ?_⟩
  change (!![(w 0)⁻¹, 0, 0; -w 1, w 0, 0; -w 2 * (w 0)⁻¹, 0, 1] : Matrix (Fin 3) (Fin 3) F) *ᵥ w = _
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hw]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hw]

theorem exists_smul_eq_e0_3 (w : Fin 3 → F) (hw : w ≠ 0) :
    ∃ g : SL(3, F), g • w = Pi.single 0 1 := by
  by_cases h0 : w 0 = 0
  · by_cases h1 : w 1 = 0
    · have h2 : w 2 ≠ 0 := by
        intro h2
        apply hw
        ext i
        fin_cases i <;> simp [h0, h1, h2]
      have hne : ((transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : F)) • w) 0 ≠ 0 := by
        rw [transvection_smul]
        simpa [h0] using h2
      obtain ⟨g, hg⟩ := exists_smul_eq_e0_of_ne _ hne
      exact ⟨g * transvection (show (0 : Fin 3) ≠ 2 by decide) 1, by rw [mul_smul, hg]⟩
    · have hne : ((transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : F)) • w) 0 ≠ 0 := by
        rw [transvection_smul]
        simpa [h0] using h1
      obtain ⟨g, hg⟩ := exists_smul_eq_e0_of_ne _ hne
      exact ⟨g * transvection (show (0 : Fin 3) ≠ 1 by decide) 1, by rw [mul_smul, hg]⟩
  · exact exists_smul_eq_e0_of_ne w h0

theorem exists_smul_eq3 (w v : Fin 3 → F) (hw : w ≠ 0) (hv : v ≠ 0) :
    ∃ A : SL(3, F), A • w = v := by
  obtain ⟨g, hg⟩ := exists_smul_eq_e0_3 w hw
  obtain ⟨g', hg'⟩ := exists_smul_eq_e0_3 v hv
  refine ⟨g'⁻¹ * g, ?_⟩
  rw [mul_smul, hg, ← hg', inv_smul_smul]

theorem natAct3_irreducible (X : Subgroup (W3 F))
    (hX : ∀ A : SL(3, F), ∀ x ∈ X, natAct3 A x ∈ X) : X = ⊥ ∨ X = ⊤ := by
  by_cases hbot : X = ⊥
  · exact Or.inl hbot
  refine Or.inr (eq_top_iff.2 fun v _ => ?_)
  obtain ⟨⟨x, hxX⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  by_cases hv : Multiplicative.toAdd v = 0
  · have : v = 1 := Multiplicative.toAdd.injective (by simpa using hv)
    rw [this]
    exact X.one_mem
  have hx0 : Multiplicative.toAdd x ≠ 0 := fun h =>
    hx1 (Subtype.ext (Multiplicative.toAdd.injective (by simpa using h)))
  obtain ⟨A, hA⟩ := exists_smul_eq3 (Multiplicative.toAdd x) (Multiplicative.toAdd v) hx0 hv
  have := hX A x hxX
  rwa [natAct3_apply, hA, ofAdd_toAdd] at this

@[expose] def ug (a b c : F) : SL(3, F) :=
  ⟨!![1, a, b; 0, 1, c; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem ug_coe (a b c : F) :
    (ug a b c : Matrix (Fin 3) (Fin 3) F) = !![1, a, b; 0, 1, c; 0, 0, 1] := rfl

theorem ug_mul (a b c a' b' c' : F) :
    ug a b c * ug a' b' c' = ug (a + a') (b + a * c' + b') (c + c') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ug_coe, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem ug_zero : ug (0 : F) 0 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ug_coe]

theorem ug_injective : Function.Injective (fun p : F × F × F => ug p.1 p.2.1 p.2.2) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h1 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 0 1) h
  have h2 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 0 2) h
  have h3 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 1 2) h
  simp [ug_coe] at h1 h2 h3
  simp [h1, h2, h3]

@[expose] def Ug (F : Type*) [Field F] : Subgroup SL(3, F) where
  carrier := Set.range (fun p : F × F × F => ug p.1 p.2.1 p.2.2)
  one_mem' := ⟨(0, 0, 0), ug_zero⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a, b, c⟩, rfl⟩ ⟨⟨a', b', c'⟩, rfl⟩
    exact ⟨(a + a', b + a * c' + b', c + c'), (ug_mul a b c a' b' c').symm⟩
  inv_mem' := by
    rintro _ ⟨⟨a, b, c⟩, rfl⟩
    refine ⟨(-a, a * c - b, -c), ?_⟩
    show ug (-a) (a * c - b) (-c) = (ug a b c)⁻¹
    apply eq_inv_of_mul_eq_one_left
    rw [ug_mul]
    have h1 : (a * c - b + -a * c + b) = 0 := by ring
    rw [h1, neg_add_cancel, neg_add_cancel]
    exact ug_zero

theorem mem_Ug {A : SL(3, F)} : A ∈ Ug F ↔ ∃ a b c : F, ug a b c = A := by
  constructor
  · rintro ⟨⟨a, b, c⟩, rfl⟩
    exact ⟨a, b, c, rfl⟩
  · rintro ⟨a, b, c, rfl⟩
    exact ⟨(a, b, c), rfl⟩

theorem card_Ug : Nat.card (Ug F) = Nat.card F ^ 3 := by
  have h : Nat.card (Ug F) = Nat.card (F × F × F) := Nat.card_range_of_injective ug_injective
  rw [h, Nat.card_prod, Nat.card_prod]
  ring

theorem Ug_isPGroup [CharP F 2] : IsPGroup 2 (Ug F) := by
  intro A
  obtain ⟨a, b, c, hA⟩ := mem_Ug.1 A.2
  refine ⟨2, ?_⟩
  apply Subtype.ext
  have h2 : (A : SL(3, F)) ^ 2 = ug 0 (a * c) 0 := by
    rw [← hA, pow_two, ug_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
    congr 1
    rw [add_assoc, add_comm (a * c) b, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have h4 : (A : SL(3, F)) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, pow_two, ug_mul]
    have h5 : a * c + 0 * 0 + a * c = 0 := by
      rw [zero_mul, add_zero]
      exact CharTwo.add_self_eq_zero _
    rw [h5, add_zero]
    exact ug_zero
  simpa using h4

theorem card_SL3 [Finite F] :
    Nat.card SL(3, F) = Nat.card F ^ 3 * ((Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1)) := by
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_SL_field 3, Nat.card_eq_fintype_card]
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  set q := Fintype.card F with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  have h1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_succ']
  have h2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_succ]
  rw [h1, h2]
  exact Nat.div_eq_of_eq_mul_left (by omega) (by ring)

theorem Ug_index_odd [CharP F 2] [Finite F] : ¬ 2 ∣ (Ug F).index := by
  have h := Subgroup.card_mul_index (Ug F)
  rw [card_Ug, card_SL3] at h
  have hq : 0 < Nat.card F ^ 3 := pow_pos Nat.card_pos 3
  have h2 : (Ug F).index = (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
    refine Nat.eq_of_mul_eq_mul_left hq ?_
    exact h
  rw [h2]
  have hev := card_F_even (F := F)
  have hpos : 0 < Nat.card F := Nat.card_pos
  have h3 : Even (Nat.card F ^ 3) := Nat.even_pow.2 ⟨hev, by norm_num⟩
  have h4 : Even (Nat.card F ^ 2) := Nat.even_pow.2 ⟨hev, by norm_num⟩
  have h5 : 1 ≤ Nat.card F ^ 3 := Nat.one_le_pow _ _ hpos
  have h6 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ hpos
  obtain ⟨k, hk⟩ := h3
  obtain ⟨l, hl⟩ := h4
  intro hd
  have hodd1 : (Nat.card F ^ 3 - 1) % 2 = 1 := by omega
  have hodd2 : (Nat.card F ^ 2 - 1) % 2 = 1 := by omega
  have := Nat.mul_mod ((Nat.card F ^ 3 - 1)) ((Nat.card F ^ 2 - 1)) 2
  rw [hodd1, hodd2] at this
  omega

theorem tq_eq_ug (b c : F) : tq b c = ug b c 0 := rfl

theorem ug_zero_zero (c : F) :
    ug 0 0 c = transvection (show (1 : Fin 3) ≠ 2 by decide) c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ug_coe, transvection_coe]

theorem ug_eq_tq_mul (a b c : F) : ug a b c = tq a (b - a * c) * ug 0 0 c := by
  rw [tq_eq_ug, ug_mul]
  congr 1 <;> ring

theorem ug_zero_zero_smul_e0 (c : F) : ug 0 0 c • (vE F 0) = vE F 0 := by
  rw [ug_zero_zero, transvection_smul]
  simp

theorem Qv_smul {v : Fin 3 → F} {r : F} (hr : r ≠ 0) : Qv (r • v) = Qv v := by
  ext A
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun x => ?_⟩
    · have : A • (r • v) = r • v := h1
      rw [smul_comm] at this
      exact smul_right_injective _ hr this
    · obtain ⟨c, hc⟩ := h2 x
      exact ⟨c * r, by rw [hc, smul_smul]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun x => ?_⟩
    · rw [smul_comm, h1]
    · obtain ⟨c, hc⟩ := h2 x
      exact ⟨c * r⁻¹, by rw [hc, smul_smul, mul_assoc, inv_mul_cancel₀ hr, mul_one]⟩

theorem Qv_conj_mem {v : Fin 3 → F} (hv : v ≠ 0) {p A : SL(3, F)} (hp : p ∈ Pt v)
    (hA : A ∈ Qv v) : p * A * p⁻¹ ∈ Qv v := by
  obtain ⟨c, hc⟩ := hp
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hv
    have : p • v = 0 := by rw [hc, zero_smul]
    have h2 := congrArg (fun x => p⁻¹ • x) this
    simpa using h2
  have := (mem_Qv_conj p A).2 hA
  rw [hc, Qv_smul hc0] at this
  exact this

theorem Qv_map_conj (γ : SL(3, F)) (v : Fin 3 → F) :
    (Qv v).map (MulAut.conj γ).toMonoidHom = Qv (γ • v) := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    exact (mem_Qv_conj γ B).2 hB
  · intro hA
    refine ⟨γ⁻¹ * A * γ, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (mem_Qv_conj γ (γ⁻¹ * A * γ)).1 (by simpa [mul_assoc] using hA)
    exact this

theorem exists_basis_matrix {u₁ u₂ u₃ : Fin 3 → F}
    (hspan : ∀ x : Fin 3 → F, ∃ a b c : F, x = a • u₁ + b • u₂ + c • u₃) :
    ∃ (Q : SL(3, F)) (r : F), r ≠ 0 ∧ Q • vE F 0 = u₁ ∧ Q • vE F 1 = u₂ ∧
      Q • vE F 2 = r • u₃ := by
  let P : Matrix (Fin 3) (Fin 3) F :=
    !![u₁ 0, u₂ 0, u₃ 0; u₁ 1, u₂ 1, u₃ 1; u₁ 2, u₂ 2, u₃ 2]
  have hP : ∀ a b c : F, P *ᵥ ![a, b, c] = a • u₁ + b • u₂ + c • u₃ := fun a b c => by
    ext i
    fin_cases i <;> simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]
  have hsurj : Function.Surjective P.mulVec := by
    intro x
    obtain ⟨a, b, c, rfl⟩ := hspan x
    exact ⟨![a, b, c], hP a b c⟩
  have hunit : IsUnit P := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hd : P.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det P).1 hunit |>.ne_zero
  let Q : SL(3, F) := ⟨P * Matrix.diagonal ![1, 1, P.det⁻¹], by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    simp [Fin.prod_univ_three, hd]⟩
  have hQ : ∀ a b c : F, Q • (![a, b, c] : Fin 3 → F) = a • u₁ + b • u₂ + (c * P.det⁻¹) • u₃ := by
    intro a b c
    change (P * Matrix.diagonal ![1, 1, P.det⁻¹]) *ᵥ ![a, b, c] = _
    rw [← Matrix.mulVec_mulVec]
    have : Matrix.diagonal ![1, 1, P.det⁻¹] *ᵥ ![a, b, c] = ![a, b, c * P.det⁻¹] := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec_diagonal, mul_comm]
    rw [this, hP]
  refine ⟨Q, P.det⁻¹, inv_ne_zero hd, ?_, ?_, ?_⟩
  · have := hQ 1 0 0
    rw [show (vE F 0) = ![1, 0, 0] by ext j; fin_cases j <;> simp [vE]]
    simpa using this
  · have := hQ 0 1 0
    rw [show (vE F 1) = ![0, 1, 0] by ext j; fin_cases j <;> simp [vE]]
    simpa using this
  · have := hQ 0 0 1
    rw [show (vE F 2) = ![0, 0, 1] by ext j; fin_cases j <;> simp [vE]]
    simpa using this

theorem Qv_sup_basis {u₁ u₂ u₃ : Fin 3 → F}
    (hspan : ∀ x : Fin 3 → F, ∃ a b c : F, x = a • u₁ + b • u₂ + c • u₃) :
    Qv u₁ ⊔ Qv u₂ ⊔ Qv u₃ = ⊤ := by
  obtain ⟨Q, r, hr, h0, h1, h2⟩ := exists_basis_matrix hspan
  have hmap : (Qv (vE F 0) ⊔ Qv (vE F 1) ⊔ Qv (vE F 2)).map (MulAut.conj Q).toMonoidHom = ⊤ := by
    rw [Qv_gen, Subgroup.map_top, MonoidHom.range_eq_top]
    exact (MulAut.conj Q).surjective
  rw [Subgroup.map_sup, Subgroup.map_sup, Qv_map_conj, Qv_map_conj, Qv_map_conj, h0, h1, h2,
    Qv_smul hr] at hmap
  exact hmap

theorem Ug_conj_index_odd [CharP F 2] [Finite F] (Q : SL(3, F)) :
    ¬ 2 ∣ ((Ug F).map (MulAut.conj Q).toMonoidHom).index := by
  rw [Subgroup.index_map_of_bijective (MulAut.conj Q).bijective]
  exact Ug_index_odd

theorem Ug_conj_le (Q : SL(3, F)) :
    (Ug F).map (MulAut.conj Q).toMonoidHom ≤ Qv (Q • vE F 0) ⊔ (Qv (Q • vE F 1) ⊓ Pt (Q • vE F 0)) := by
  rintro _ ⟨A, hA, rfl⟩
  obtain ⟨a, b, c, rfl⟩ := mem_Ug.1 hA
  rw [ug_eq_tq_mul]
  have h1 : (MulAut.conj Q) (tq a (b - a * c)) ∈ Qv (Q • vE F 0) := by
    have := (mem_Qv_conj Q (tq a (b - a * c))).2 (tq_mem_Qv _ _)
    simpa [MulAut.conj_apply] using this
  have h2 : (MulAut.conj Q) (ug 0 0 c) ∈ Qv (Q • vE F 1) ⊓ Pt (Q • vE F 0) := by
    refine ⟨?_, ?_⟩
    · have := (mem_Qv_conj Q (ug 0 0 c)).2 (by rw [ug_zero_zero]; exact transvection_mem_Qv _ c)
      simpa [MulAut.conj_apply] using this
    · refine ⟨1, ?_⟩
      rw [one_smul, MulAut.conj_apply, mul_smul, mul_smul, inv_smul_smul, ug_zero_zero_smul_e0]
  rw [map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)

theorem c3_mem_commutator [Finite F] [CharP F 2] : c3 F ∈ commutator SL(2, F) := by
  rcases card_two_or_exists_sq_ne_one (F := F) with h2 | ⟨a, ha0, ha1⟩
  · rw [commutator_eq_zpowers_c3 h2]
    exact Subgroup.mem_zpowers _
  · rw [Matrix.SL2.commutator_eq_top ha0 ha1]
    exact Subgroup.mem_top _

theorem tq_inv [CharP F 2] (b c : F) : (tq b c)⁻¹ = tq b c :=
  inv_eq_of_mul_eq_one_right (Qv_sq _ (tq_mem_Qv b c))

theorem tq_mul_blk_c3 [CharP F 2] (b₀ c₀ : F) :
    tq b₀ c₀ * (blk (c3 F) * (tq b₀ c₀)⁻¹ * (blk (c3 F))⁻¹) = tq c₀ (c₀ + b₀) := by
  rw [tq_inv, blk_conj_tq, ← tq_add, c3_smul]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  rw [add_comm c₀ b₀, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

end CFSG.Quasithin.SL3Model

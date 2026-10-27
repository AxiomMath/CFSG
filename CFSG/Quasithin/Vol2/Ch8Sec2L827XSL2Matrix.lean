module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.H13.L827X.SL2Orb
open scoped MatrixGroups

theorem sq_eq_one_of_det_one {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (hdet : M.det = 1) (hsq : M * M = 1) (h2 : (2 : F) ≠ 0) : M = 1 ∨ M = -1 := by
  have hdet' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact hdet
  have h00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = 1 := by
    have h := congrFun (congrFun hsq 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have h01 : M 0 0 * M 0 1 + M 0 1 * M 1 1 = 0 := by
    have h := congrFun (congrFun hsq 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have h10 : M 1 0 * M 0 0 + M 1 1 * M 1 0 = 0 := by
    have h := congrFun (congrFun hsq 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  have h11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 = 1 := by
    have h := congrFun (congrFun hsq 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  by_cases hs : M 0 0 + M 1 1 = 0
  · exfalso
    apply h2
    linear_combination (-1 : F) * h00 - hdet' + M 0 0 * hs
  · have hb : M 0 1 = 0 := by
      have h : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination h01
      exact (mul_eq_zero.mp h).resolve_right hs
    have hc : M 1 0 = 0 := by
      have h : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination h10
      exact (mul_eq_zero.mp h).resolve_right hs
    have ha : M 0 0 * M 0 0 = 1 := by linear_combination h00 - M 1 0 * hb
    have had : M 0 0 * M 1 1 = 1 := by linear_combination hdet' + M 1 0 * hb
    have hda : M 0 0 = M 1 1 := by linear_combination (M 1 1) * ha - (M 0 0) * had
    rcases mul_self_eq_one_iff.mp ha with h | h
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, h, ← hda]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, h, ← hda]

theorem center_map_eq_pm {F K : Type*} [Field F] [Field K] (σ : F →+* K)
    (hσ : Function.Injective σ) (M : Matrix.SpecialLinearGroup (Fin 2) F)
    (hM : Matrix.SpecialLinearGroup.map σ M ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) :
    (M : Matrix (Fin 2) (Fin 2) F) = 1 ∨ (M : Matrix (Fin 2) (Fin 2) F) = -1 := by
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hM
  have hent : ∀ i j, Matrix.scalar (Fin 2) r i j = σ (M i j) := by
    intro i j
    rw [hr]
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have hr01 : Matrix.scalar (Fin 2) r 0 1 = 0 := by simp [Matrix.scalar_apply]
  have hr10 : Matrix.scalar (Fin 2) r 1 0 = 0 := by simp [Matrix.scalar_apply]
  have hr00 : Matrix.scalar (Fin 2) r 0 0 = r := by simp [Matrix.scalar_apply]
  have hr11 : Matrix.scalar (Fin 2) r 1 1 = r := by simp [Matrix.scalar_apply]
  have e01 : σ (M 0 1) = σ 0 := by rw [map_zero, ← hent 0 1, hr01]
  have e10 : σ (M 1 0) = σ 0 := by rw [map_zero, ← hent 1 0, hr10]
  have e00 : σ (M 0 0) = r := by rw [← hent 0 0, hr00]
  have e11 : σ (M 1 1) = r := by rw [← hent 1 1, hr11]
  have hM01 : M 0 1 = 0 := hσ e01
  have hM10 : M 1 0 = 0 := hσ e10
  have hM00 : M 0 0 = M 1 1 := hσ (e00.trans e11.symm)
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact M.prop
  have hsq : M 0 0 * M 0 0 = 1 := by
    linear_combination hdet + M 0 0 * hM00 + M 1 0 * hM01
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM01, hM10, h, ← hM00]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM01, hM10, h, ← hM00]

theorem card_SL_two (K : Type*) [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Nat.card_eq_fintype_card]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Fintype.card K
  have hsub : q ^ 2 - q = q * (q - 1) := by
    rw [sq, Nat.mul_sub_one]
  have hpos : 0 < q - 1 := by omega
  rw [hsub, show (q ^ 2 - 1) * (q * (q - 1)) = q * (q ^ 2 - 1) * (q - 1) by ring]
  exact Nat.mul_div_cancel _ hpos

private lemma eq_of_mul_self_eq_one_iff {K : Type*} [Field K] {a b : K} (ha : a * a = 1)
    (hb : b * b = 1) (h : a = 1 ↔ b = 1) : a = b := by
  rcases mul_self_eq_one_iff.mp ha with rfl | rfl <;>
    rcases mul_self_eq_one_iff.mp hb with rfl | rfl
  · rfl
  · exact (h.mp rfl).symm
  · exact h.mpr rfl
  · rfl

theorem card_center_SL_two_le (K : Type*) [Field K] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) ≤ 2 := by
  classical
  have hcent : ∀ x : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K),
      (x : Matrix.SpecialLinearGroup (Fin 2) K) 0 0 * (x : Matrix.SpecialLinearGroup (Fin 2) K) 0 0
        = 1 := by
    intro x
    obtain ⟨r, hr, hreq⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp x.2
    have h00 : (x : Matrix.SpecialLinearGroup (Fin 2) K) 0 0 = r := by
      rw [← hreq]; simp [Matrix.scalar_apply]
    rw [h00, ← sq]
    simpa using hr
  let f : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) → Bool :=
    fun x => decide ((x : Matrix.SpecialLinearGroup (Fin 2) K) 0 0 = 1)
  have hf : Function.Injective f := by
    intro x y hxy
    have hiff : (x : Matrix.SpecialLinearGroup (Fin 2) K) 0 0 = 1 ↔
        (y : Matrix.SpecialLinearGroup (Fin 2) K) 0 0 = 1 := decide_eq_decide.mp hxy
    have hab := eq_of_mul_self_eq_one_iff (hcent x) (hcent y) hiff
    apply Subtype.ext
    apply Subtype.ext
    rw [← Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center x.2 0,
      ← Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center y.2 0, hab]
  have h := Nat.card_le_card_of_injective f hf
  simpa using h

theorem card_SL_le_two_mul_PSL (K : Type*) [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) ≤
      2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  rw [← Subgroup.card_mul_index (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))]
  exact Nat.mul_le_mul (card_center_SL_two_le K) le_rfl

theorem exists_involution_psl (K : Type*) [Field K] :
    ∃ h : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K, h ≠ 1 ∧ h * h = 1 := by
  let g : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  refine ⟨QuotientGroup.mk g, ?_, ?_⟩
  · intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
    have h01 := congrFun (congrFun hr 0) 1
    simp [g, Matrix.scalar_apply] at h01
  · rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨-1, by simp, ?_⟩
    have hJJ : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; -1, 0] = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hgg : ((g * g : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = -1 :=
      hJJ
    rw [hgg]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

theorem card_alternatingGroup_fin_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem exists_involution_alt_five : ∃ τ : alternatingGroup (Fin 5), τ ≠ 1 ∧ τ * τ = 1 := by
  have hne : Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3 ≠ 1 := by decide
  have hsq : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) *
      (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) = 1 := by decide
  have hmem : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul,
      Equiv.Perm.sign_swap (show (0 : Fin 5) ≠ 1 by decide),
      Equiv.Perm.sign_swap (show (2 : Fin 5) ≠ 3 by decide)]
    decide
  refine ⟨⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3, hmem⟩, ?_, ?_⟩
  · intro h
    exact hne (congrArg Subtype.val h)
  · exact Subtype.ext hsq

end CFSG.Quasithin.H13.L827X.SL2Orb

end

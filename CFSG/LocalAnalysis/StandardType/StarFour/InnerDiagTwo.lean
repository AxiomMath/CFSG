module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeTypeA

public section

namespace CFSG.StandardType.StarFour

open CFSG.StandardType

open Matrix

open scoped CharTwo

private theorem fin01 : (0 : Fin (1 + 1)) ≠ 1 := by decide

private theorem fin10 : (1 : Fin (1 + 1)) ≠ 0 := by decide

private def x01 {F : Type} [Field F] (t : F) : Matrix.SpecialLinearGroup (Fin (1 + 1)) F :=
  Matrix.SpecialLinearGroup.transvection fin01 t

private def x10 {F : Type} [Field F] (t : F) : Matrix.SpecialLinearGroup (Fin (1 + 1)) F :=
  Matrix.SpecialLinearGroup.transvection fin10 t

private def weyl (F : Type) [Field F] : Matrix.SpecialLinearGroup (Fin (1 + 1)) F :=
  x01 (F := F) 1 * x10 (F := F) 1 * x01 (F := F) 1

private def WW (F : Type) [Field F] (u v : F) :
    Matrix.SpecialLinearGroup (Fin (1 + 1)) F :=
  x01 (F := F) u * x10 (F := F) v * x01 (F := F) u

private theorem x01_coe (F : Type) [Field F] (t : F) :
    ((x01 (F := F) t) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) F) = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x01, Matrix.SpecialLinearGroup.transvection_coe, fin01]

private theorem x10_coe (F : Type) [Field F] (t : F) :
    ((x10 (F := F) t) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) F) = !![1, 0; t, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [x10, Matrix.SpecialLinearGroup.transvection_coe, fin10]

private theorem weyl_coe (F : Type) [Field F] [CharP F 2] :
    ((weyl F) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) F) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, x01, x10, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply, Matrix.single_apply, fin01, fin10]

private theorem WW_coe (F : Type) [Field F] [CharP F 2] (u v : F) :
    ((WW F u v) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) F) =
      !![1 + u * v, u ^ 2 * v; v, 1 + u * v] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WW, x01, x10, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply, Matrix.single_apply, fin01, fin10, mul_add, add_mul]
  all_goals ring_nf
  all_goals simp [CharTwo.two_eq_zero]

private theorem weyl_mul_self (F : Type) [Field F] [CharP F 2] : weyl F * weyl F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, weyl_coe, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CharTwo.add_self_eq_zero]

private theorem weyl_conj (F : Type) [Field F] [CharP F 2] (a : F) :
    weyl F * x01 (F := F) a * (weyl F)⁻¹ = x10 (F := F) a := by
  have hinv : (weyl F)⁻¹ = weyl F := inv_eq_of_mul_eq_one_right (weyl_mul_self F)
  rw [hinv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, weyl_coe, x01_coe,
    x10_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CharTwo.add_self_eq_zero]

private theorem exists_conj_eq_conjSL_two_aux {F : Type} [Field F] [CharP F 2] {G : Type*}
    [Group G] (ψ : Matrix.SpecialLinearGroup (Fin (1 + 1)) F →* G)
    (hψ : Function.Injective ψ) {x : G} {χ : Fin (1 + 1) → Fin (1 + 1) → F}
    (hχ : ∀ (i j : Fin (1 + 1)) (hij : i ≠ j) (t : F),
      x⁻¹ * ψ (Matrix.SpecialLinearGroup.transvection hij t) * x =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t))) :
    χ 0 1 * χ 1 0 = 1 := by
  classical
  let β : Matrix.SpecialLinearGroup (Fin (1 + 1)) F →* G :=
    (MulAut.conj x⁻¹).toMonoidHom.comp ψ
  have hβ : ∀ u, β u = x⁻¹ * ψ u * x := fun u => by simp [β]
  have hχ' : ∀ (i j : Fin (1 + 1)) (hij : i ≠ j) (t : F),
      β (Matrix.SpecialLinearGroup.transvection hij t) =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t)) :=
    fun i j hij t => (hβ _).trans (hχ i j hij t)
  have hne : ∀ (i j : Fin (1 + 1)) (hij : i ≠ j), χ i j ≠ 0 := by
    intro i j hij h0
    have h1 : ψ (Matrix.SpecialLinearGroup.transvection hij (1 : F)) = 1 := by
      calc ψ (Matrix.SpecialLinearGroup.transvection hij 1)
          = x * (x⁻¹ * ψ (Matrix.SpecialLinearGroup.transvection hij 1) * x) * x⁻¹ := by
            group
        _ = 1 := by
            rw [hχ i j hij 1, h0, zero_mul,
              Matrix.SpecialLinearGroup.transvection_coeff_zero, map_one]
            group
    have h2 : Matrix.SpecialLinearGroup.transvection hij (1 : F) = 1 :=
      hψ (by rw [h1, map_one])
    have h3 := congrFun (congrFun (congrArg Subtype.val h2) i) j
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply_ne hij] at h3
  have hβweyl : β (weyl F) = ψ (WW F (χ 0 1) (χ 1 0)) := by
    simp only [weyl, WW, x01, x10]
    simp only [map_mul]
    rw [hχ' 0 1 fin01 1, hχ' 1 0 fin10 1]
    simp only [mul_one]
  have hconj : ∀ a : F, WW F (χ 0 1) (χ 1 0) * x01 (F := F) (χ 0 1 * a) *
      (WW F (χ 0 1) (χ 1 0))⁻¹ = x10 (F := F) (χ 1 0 * a) := by
    intro a
    apply hψ
    have h1 := congrArg β (weyl_conj (F := F) a)
    simp only [x01, x10] at h1
    rw [map_mul, map_mul, map_inv, hβweyl, hχ' 0 1 fin01 a, hχ' 1 0 fin10 a] at h1
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact h1
  have hEq : WW F (χ 0 1) (χ 1 0) * x01 (F := F) (χ 0 1) =
      x10 (F := F) (χ 1 0) * WW F (χ 0 1) (χ 1 0) := by
    have h := hconj 1
    rw [mul_one, mul_one] at h
    calc WW F (χ 0 1) (χ 1 0) * x01 (F := F) (χ 0 1)
        = WW F (χ 0 1) (χ 1 0) * x01 (F := F) (χ 0 1) *
            (WW F (χ 0 1) (χ 1 0))⁻¹ * WW F (χ 0 1) (χ 1 0) := by group
      _ = x10 (F := F) (χ 1 0) * WW F (χ 0 1) (χ 1 0) := by rw [h]
  have hWW : WW F (χ 0 1) (χ 1 0) * x01 (F := F) (χ 0 1) =
      x01 (F := F) (χ 0 1) * x10 (F := F) (χ 1 0) := by
    have hxx : x01 (F := F) (χ 0 1) * x01 (F := F) (χ 0 1) = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, x01_coe, Matrix.SpecialLinearGroup.coe_one,
        Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [CharTwo.add_self_eq_zero]
    unfold WW
    rw [show x01 (F := F) (χ 0 1) * x10 (F := F) (χ 1 0) * x01 (F := F) (χ 0 1) *
        x01 (F := F) (χ 0 1) =
        (x01 (F := F) (χ 0 1) * x10 (F := F) (χ 1 0)) *
          (x01 (F := F) (χ 0 1) * x01 (F := F) (χ 0 1)) by group,
      hxx, mul_one]
  have hcross : x01 (F := F) (χ 0 1) * x10 (F := F) (χ 1 0) =
      x10 (F := F) (χ 1 0) * WW F (χ 0 1) (χ 1 0) := by
    rw [← hWW]
    exact hEq
  have hvne : χ 1 0 ≠ 0 := hne 1 0 fin10
  have hmat := congrFun (congrFun (congrArg Subtype.val hcross) 1) 0
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, x01_coe, x10_coe,
    WW_coe] at hmat
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at hmat
  simp at hmat
  rcases hmat with h0 | h1
  · exact absurd h0 hvne
  · exact (CharTwo.add_eq_zero.mp h1).symm

theorem exists_conj_eq_conjSL_two {F : Type} [Field F] [CharP F 2] {G : Type*} [Group G]
    (ψ : Matrix.SpecialLinearGroup (Fin (1 + 1)) F →* G) (hψ : Function.Injective ψ) {x : G}
    {χ : Fin (1 + 1) → Fin (1 + 1) → F}
    (hχ : ∀ (i j : Fin (1 + 1)) (hij : i ≠ j) (t : F),
      x⁻¹ * ψ (Matrix.SpecialLinearGroup.transvection hij t) * x =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t))) :
    ∃ D : GL (Fin (1 + 1)) F, ∀ u, x⁻¹ * ψ u * x = ψ (InnerDiagA.conjSL D u) := by
  classical
  have huv : χ 0 1 * χ 1 0 = 1 := exists_conj_eq_conjSL_two_aux ψ hψ hχ
  have hvu : χ 1 0 = (χ 0 1)⁻¹ := eq_inv_of_mul_eq_one_right huv
  let d : Fin (1 + 1) → Fˣ := fun k =>
    if k = 0 then Units.mk0 (χ 0 1) (by
      intro h0
      rw [h0, zero_mul] at huv
      exact zero_ne_one huv) else 1
  have hd0 : (d 0 : F) = χ 0 1 := by simp [d]
  have hd1 : (d 1 : F) = 1 := by simp [d, fin10]
  have hd : ∀ (i j : Fin (1 + 1)) (hij : i ≠ j), (d i : F) = χ i j * (d j : F) := by
    have h01 : ∀ i : Fin (1 + 1), i = 0 ∨ i = 1 := by
      intro i
      fin_cases i
      · left; rfl
      · right; rfl
    intro i j hij
    rcases h01 i with rfl | rfl <;> rcases h01 j with rfl | rfl
    · exact (hij rfl).elim
    · rw [hd0, hd1, mul_one]
    · rw [hd1, hd0, mul_comm (χ 1 0) (χ 0 1), huv]
    · exact (hij rfl).elim
  have harg : ∀ (i j : Fin (1 + 1)) (hij : i ≠ j) (t : F),
      χ i j * t = (d i : F) * t * ((d j : F)⁻¹) := by
    have h01 : ∀ i : Fin (1 + 1), i = 0 ∨ i = 1 := by
      intro i
      fin_cases i
      · left; rfl
      · right; rfl
    intro i j hij t
    rcases h01 i with rfl | rfl <;> rcases h01 j with rfl | rfl
    · exact (hij rfl).elim
    · rw [hd0, hd1, inv_one, mul_one]
    · rw [hd1, hd0, one_mul, hvu, mul_comm]
    · exact (hij rfl).elim
  let β : Matrix.SpecialLinearGroup (Fin (1 + 1)) F →* G :=
    (MulAut.conj x⁻¹).toMonoidHom.comp ψ
  have hβ : ∀ u, β u = x⁻¹ * ψ u * x := fun u => by simp [β]
  have hχ' : ∀ (i j : Fin (1 + 1)) (hij : i ≠ j) (t : F),
      β (Matrix.SpecialLinearGroup.transvection hij t) =
        ψ (Matrix.SpecialLinearGroup.transvection hij (χ i j * t)) :=
    fun i j hij t => (hβ _).trans (hχ i j hij t)
  refine ⟨InnerDiagA.diagGL d, fun u => ?_⟩
  have hβψ : β = ψ.comp (InnerDiagA.conjSL (InnerDiagA.diagGL d)) := by
    refine MonoidHom.eq_of_eqOn_dense
      Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field ?_
    rintro _ ⟨⟨i, j, hij, t⟩, rfl⟩
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, hχ', MonoidHom.comp_apply,
      InnerDiagA.conjSL_diagGL_transvection, Units.val_inv_eq_inv_val]
    exact congrArg (fun s : F => ψ (Matrix.SpecialLinearGroup.transvection hij s))
      (harg i j hij t)
  rw [← hβ, hβψ, MonoidHom.comp_apply]

end CFSG.StandardType.StarFour

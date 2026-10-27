module

public import CFSG.Assembly.GL83LieDefs
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.CharP.Lemmas
import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

theorem ggLieSU3Fixed_pow_succ_of_conj_diag {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) {z : GL (Fin 4) K}
    (hz : z ∈ LargeEvenSUGroup (Fin 4) K (2 ^ n)) (g : GL (Fin 4) K) (k : Fin 4) {β : K}
    (hdiag : ((g * z * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (hk : ((g * z * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) k k = 1)
    (hβ : ∀ i, i ≠ k → ((g * z * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i = β) :
    β ^ (2 ^ n + 1) = 1 := by
  classical
  have hn : 1 ≤ n := by
    by_contra hlt
    have hn0 : n = 0 := by omega
    subst hn0
    haveI : Fintype K := Fintype.ofFinite K
    have hcard : 1 < Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    rw [pow_zero, one_pow] at hK
    omega
  have h : UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, hn, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨_, hu⟩ :=
    (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1
      (show z ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n K 4 from hz)
  have h2 : (2 : K) = 0 := by
    haveI : CharP K 2 := h.charP
    exact CharP.cast_eq_zero K 2
  have h3 : (3 : K) = 1 := by
    have : (3 : K) = (2 : K) + 1 := by norm_num
    rw [this, h2, zero_add]
  let Z : Matrix (Fin 4) (Fin 4) K := (z : GL (Fin 4) K)
  let D : Matrix (Fin 4) (Fin 4) K :=
    ((g * z * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  let M : Matrix (Fin 4) (Fin 4) K :=
    (((g * z * g⁻¹)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  let d : Fin 4 → K := fun i => if i = k then 1 else β
  have hDdiag : D.IsDiag := hdiag
  have hDkk : D k k = 1 := hk
  have hDii : ∀ i, i ≠ k → D i i = β := hβ
  have hD_eq : D = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
      change D i i = (if i = k then 1 else β)
      by_cases hik : i = k
      · rw [if_pos hik, hik]; exact hDkk
      · rw [if_neg hik]; exact hDii i hik
    · rw [Matrix.diagonal_apply_ne d hij]
      exact hDdiag hij
  have htrD : D.trace = 1 + β := by
    rw [hD_eq, Matrix.trace_diagonal]
    change (∑ i : Fin 4, (if i = k then 1 else β)) = 1 + β
    fin_cases k <;>
      (simp only [Fin.sum_univ_four]
       simp
       ring_nf
       simp [h2, h3])
  have hDM : D * M = 1 := by
    show (((g * z * g⁻¹ : GL (Fin 4) K) * (g * z * g⁻¹ : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = 1
    rw [mul_inv_cancel, Units.val_one]
  have hDMdiag : Matrix.diagonal d * M = 1 := by
    rw [← hD_eq]; exact hDM
  have hβ0 : β ≠ 0 := by
    have key : ∀ i, i ≠ k → β ≠ 0 := by
      intro i hik
      have hh := congrFun (congrFun hDMdiag i) i
      rw [Matrix.diagonal_mul, Matrix.one_apply, if_pos rfl] at hh
      have hdi : d i = β := by
        change (if i = k then 1 else β) = β
        rw [if_neg hik]
      rw [hdi] at hh
      exact left_ne_zero_of_mul (by rw [hh]; exact one_ne_zero)
    fin_cases k
    · exact key 1 (by decide)
    · exact key 0 (by decide)
    · exact key 0 (by decide)
    · exact key 0 (by decide)
  have hd_ne : ∀ i, d i ≠ 0 := by
    intro i
    by_cases hik : i = k
    · have hdi : d i = 1 := by
        change (if i = k then 1 else β) = 1
        rw [if_pos hik]
      rw [hdi]
      exact one_ne_zero
    · have hdi : d i = β := by
        change (if i = k then 1 else β) = β
        rw [if_neg hik]
      rw [hdi]
      exact hβ0
  have hM_eq : M = Matrix.diagonal (fun i => (d i)⁻¹) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have h := congrFun (congrFun hDMdiag i) i
      rw [Matrix.diagonal_mul, Matrix.one_apply, if_pos rfl] at h
      rw [Matrix.diagonal_apply_eq]
      exact ((mul_eq_one_iff_inv_eq₀ (hd_ne i)).mp h).symm
    · have h := congrFun (congrFun hDMdiag i) j
      rw [Matrix.diagonal_mul, Matrix.one_apply, if_neg hij] at h
      rw [Matrix.diagonal_apply_ne _ hij]
      exact (mul_eq_zero.mp h).resolve_left (hd_ne i)
  have htrM : M.trace = 1 + β⁻¹ := by
    rw [hM_eq, Matrix.trace_diagonal]
    change (∑ i : Fin 4, (if i = k then 1 else β)⁻¹) = 1 + β⁻¹
    fin_cases k <;>
      (simp only [Fin.sum_univ_four]
       simp
       ring_nf
       simp [h2, h3])
  have hWZ : (Z.map h.bar).transpose * Z = 1 := hu
  have hZinv : Z * ((z⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    show (z : Matrix (Fin 4) (Fin 4) K) * ((z⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinvZ : ((z⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * Z = 1 := by
    show ((z⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (z : Matrix (Fin 4) (Fin 4) K) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hW_eq : (Z.map h.bar).transpose = ((z⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [← Matrix.inv_eq_left_inv hWZ, Matrix.inv_eq_left_inv hinvZ]
  have htrZ_D : Z.trace = D.trace := by
    show (z : Matrix (Fin 4) (Fin 4) K).trace = ((g * z * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace
    rw [show ((g * z * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (g : Matrix (Fin 4) (Fin 4) K) * (z : Matrix (Fin 4) (Fin 4) K) * ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      from by simp only [Units.val_mul]]
    exact (Matrix.trace_units_conj g (z : Matrix (Fin 4) (Fin 4) K)).symm
  have htr_z_inv : (((z⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).trace = h.bar D.trace := by
    rw [← hW_eq, Matrix.trace_transpose]
    exact (AddMonoidHom.map_trace h.bar Z).symm.trans (congrArg h.bar htrZ_D)
  have htrM_z : M.trace = (((z⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)).trace := by
    show (((g * z * g⁻¹)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace =
      ((z⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace
    rw [show ((g * z * g⁻¹ : GL (Fin 4) K)⁻¹) = g * z⁻¹ * g⁻¹ from by group]
    rw [show ((g * z⁻¹ * g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (g : Matrix (Fin 4) (Fin 4) K) * ((z⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      from by simp only [Units.val_mul]]
    exact Matrix.trace_units_conj g ((z⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  have hrel : β⁻¹ = β ^ (2 ^ n) := by
    have h1 : 1 + β⁻¹ = h.bar (1 + β) := by
      rw [← htrM, htrM_z, htr_z_inv, htrD]
    rw [map_add, map_one, h.bar_apply β] at h1
    exact add_left_cancel h1
  rw [pow_succ, ← hrel]
  exact inv_mul_cancel₀ hβ0

end CFSG.StandardType

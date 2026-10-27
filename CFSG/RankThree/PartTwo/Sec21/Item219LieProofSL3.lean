module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item219LieProof

open Matrix Subgroup
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def slDiag {ω : K} (hω : ω ^ 3 = 1) : SL(3, K) :=
  ⟨Matrix.diagonal ![1, ω, ω ^ 2], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, one_mul]
    linear_combination hω⟩

@[expose] def slPerm : SL(3, K) :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by simp [Matrix.det_fin_three]⟩

@[expose] def slScalar {ω : K} (hω : ω ^ 3 = 1) : SL(3, K) :=
  ⟨Matrix.scalar (Fin 3) ω, by
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hω]⟩

theorem coe_slDiag {ω : K} (hω : ω ^ 3 = 1) :
    ((slDiag hω : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![1, ω, ω ^ 2] := rfl

theorem coe_slPerm :
    ((slPerm : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := rfl

theorem coe_slScalar {ω : K} (hω : ω ^ 3 = 1) :
    ((slScalar hω : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) ω := rfl

theorem slDiag_pow_three {ω : K} (hω : ω ^ 3 = 1) : slDiag hω ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_slDiag, Matrix.diagonal_pow,
    Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simp
  · simpa using hω
  · simp only [Fin.reduceFinMk, Matrix.cons_val, Pi.pow_apply]
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω, one_pow]

theorem slPerm_pow_three : (slPerm : SL(3, K)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_slPerm, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem slScalar_pow_three {ω : K} (hω : ω ^ 3 = 1) : slScalar hω ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_slScalar, Matrix.SpecialLinearGroup.coe_one,
    ← map_pow, hω, map_one]

theorem slScalar_commute {ω : K} (hω : ω ^ 3 = 1) (M : SL(3, K)) :
    Commute (slScalar hω) M :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_slScalar]
    exact Matrix.scalar_commute ω (fun r => Commute.all _ r) _)

theorem slPerm_mul_slDiag {ω : K} (hω : ω ^ 3 = 1) :
    slPerm * slDiag hω = slScalar hω * slDiag hω * slPerm := by
  have hω' : ω * (ω * ω) = 1 := by rw [← hω]; ring
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_slPerm, coe_slDiag, coe_slScalar]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.scalar_apply, sq, hω']

theorem isPGroup_zpowers_of_pow_three {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) :
    IsPGroup 3 (zpowers g) := by
  rintro ⟨x, hx⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  refine ⟨1, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

theorem isPGroup_heis {ω : K} (hω : ω ^ 3 = 1) :
    IsPGroup 3 ↥(zpowers (slPerm : SL(3, K)) ⊔ (zpowers (slDiag hω) ⊔ zpowers (slScalar hω))) := by
  have hN : (zpowers (slScalar hω)).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    rw [((slScalar_commute hω g).zpow_left k).symm.eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) k⟩
  have hNp : IsPGroup 3 ↥(zpowers (slDiag hω) ⊔ zpowers (slScalar hω)) :=
    IsPGroup.to_sup_of_normal_right (isPGroup_zpowers_of_pow_three (slDiag_pow_three hω))
      (isPGroup_zpowers_of_pow_three (slScalar_pow_three hω))
  refine IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_three slPerm_pow_three) hNp ?_
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  have h1 : ((MulAut.conj (slPerm : SL(3, K)) : SL(3, K) →* SL(3, K)) (slDiag hω)) =
      slScalar hω * slDiag hω := by
    change slPerm * slDiag hω * slPerm⁻¹ = _
    rw [slPerm_mul_slDiag, mul_inv_cancel_right]
  have h2 : ((MulAut.conj (slPerm : SL(3, K)) : SL(3, K) →* SL(3, K)) (slScalar hω)) =
      slScalar hω := by
    change slPerm * slScalar hω * slPerm⁻¹ = _
    rw [← (slScalar_commute hω slPerm).eq, mul_inv_cancel_right]
  rw [h1, h2]
  refine le_antisymm (sup_le ?_ le_sup_right) (sup_le ?_ le_sup_right)
  · rw [Subgroup.zpowers_le]
    exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (mem_zpowers _))
  · rw [Subgroup.zpowers_le]
    have hm : (slScalar hω)⁻¹ * (slScalar hω * slDiag hω) ∈
        zpowers (slScalar hω * slDiag hω) ⊔ zpowers (slScalar hω) :=
      mul_mem (inv_mem (mem_sup_right (mem_zpowers _))) (mem_sup_left (mem_zpowers _))
    rwa [inv_mul_cancel_left] at hm

theorem eq_scalar_of_commute {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    {M : Matrix (Fin 3) (Fin 3) K}
    (hD : M * Matrix.diagonal ![1, ω, ω ^ 2] = Matrix.diagonal ![1, ω, ω ^ 2] * M)
    (hP : M * !![0, 1, 0; 0, 0, 1; 1, 0, 0] = !![0, 1, 0; 0, 0, 1; 1, 0, 0] * M) :
    M = Matrix.scalar (Fin 3) (M 0 0) := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h
    apply hω1
    have h3 : ω ^ 3 = ω * ω ^ 2 := by ring
    rw [h, mul_one, hω3] at h3
    exact h3.symm
  have hωω : ω ^ 2 ≠ ω := by
    intro h
    apply hω1
    have : ω * (ω - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h' | h'
    · exact absurd h' hω0
    · exact sub_eq_zero.1 h'
  have e : ∀ i j, M i j * ![1, ω, ω ^ 2] j = ![1, ω, ω ^ 2] i * M i j := fun i j => by
    have := congrFun (congrFun hD i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    have h := e i j
    have key : ∀ a b : K, a ≠ b → M i j * a = b * M i j → M i j = 0 := fun a b hab h' => by
      have : M i j * (a - b) = 0 := by linear_combination h'
      rcases mul_eq_zero.1 this with h'' | h''
      · exact h''
      · exact absurd (sub_eq_zero.1 h'') hab
    fin_cases i <;> fin_cases j <;> simp at hij h
    · exact key ω 1 hω1 (by simpa using h)
    · exact key (ω ^ 2) 1 hω2 (by simpa using h)
    · exact key 1 ω (Ne.symm hω1) (by simpa using h)
    · exact key (ω ^ 2) ω hωω h
    · exact key 1 (ω ^ 2) (Ne.symm hω2) (by simpa using h)
    · exact key ω (ω ^ 2) (Ne.symm hωω) h
  have h01 := congrFun (congrFun hP 0) 1
  have h12 := congrFun (congrFun hP 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h01 h12
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, hoff, h01, h12]

open scoped Pointwise in
theorem exists_map_conj_le_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (Q : Sylow p G) (E : Subgroup G) (hE : IsPGroup p E) :
    ∃ y : G, E.map (MulAut.conj y).toMonoidHom ≤ Q := by
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  refine ⟨g, ?_⟩
  have hgS : (g • S : Sylow p G).toSubgroup = S.toSubgroup.map (MulAut.conj g).toMonoidHom := rfl
  rw [hg] at hgS
  rw [hgS]
  exact Subgroup.map_mono hES

theorem exists_eq_scalar_of_commute_sylow [Finite K] {ω : K} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (P : Sylow 3 SL(3, K)) {z : SL(3, K)} (hz : ∀ p ∈ (P : Subgroup SL(3, K)), z * p = p * z) :
    ∃ c : K, (z : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_map_conj_le_sylow P _ (isPGroup_heis hω3)
  have hconj : ∀ g ∈ zpowers (slPerm : SL(3, K)) ⊔ (zpowers (slDiag hω3) ⊔
      zpowers (slScalar hω3)), (y⁻¹ * z * y) * g = g * (y⁻¹ * z * y) := by
    intro g hg
    have h1 := hz _ (hy ⟨g, hg, rfl⟩)
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    calc y⁻¹ * z * y * g = y⁻¹ * (z * (y * g * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * g * y⁻¹) * z) * y := by rw [h1]
      _ = g * (y⁻¹ * z * y) := by group
  have hD := congrArg (fun A : SL(3, K) => (A : Matrix (Fin 3) (Fin 3) K))
    (hconj _ (mem_sup_right (mem_sup_left (mem_zpowers _))))
  have hP := congrArg (fun A : SL(3, K) => (A : Matrix (Fin 3) (Fin 3) K))
    (hconj _ (mem_sup_left (mem_zpowers _)))
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_slDiag, coe_slPerm] at hD hP
  set M := ((y⁻¹ * z * y : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) with hM
  have hMs := eq_scalar_of_commute hω3 hω1 (M := M) (by simpa [hM] using hD)
    (by simpa [hM] using hP)
  obtain ⟨c, hc⟩ : ∃ c, M = Matrix.scalar (Fin 3) c := ⟨_, hMs⟩
  refine ⟨c, ?_⟩
  have hz' : z = y * (y⁻¹ * z * y) * y⁻¹ := by group
  rw [hz', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← hM, hc,
    ← (Matrix.scalar_commute c (fun r => Commute.all _ r) (y : Matrix (Fin 3) (Fin 3) K)).eq,
    mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, mul_one]

end CFSG.RankThree.PartTwo.Sec21.Item219LieProof

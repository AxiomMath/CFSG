module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res11

theorem eq_neg_one_of_mul_self_eq_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {M : Matrix (Fin 2) (Fin 2) F} (hM : M * M = 1) (hdet : M.det = 1) (hM1 : M ≠ 1) :
    M = -1 := by
  have e11 := congrFun (congrFun hM 0) 0
  have e12 := congrFun (congrFun hM 0) 1
  have e21 := congrFun (congrFun hM 1) 0
  have e22 := congrFun (congrFun hM 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e11 e12 e21 e22
  rw [Matrix.det_fin_two] at hdet
  have hsa : M 0 0 * (M 0 0 + M 1 1) = 2 := by linear_combination e11 + hdet
  have hs : M 0 0 + M 1 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsa
    exact h2 hsa.symm
  have hb : M 0 1 = 0 := by
    have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e12
    exact (mul_eq_zero.mp this).resolve_right hs
  have hc : M 1 0 = 0 := by
    have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e21
    exact (mul_eq_zero.mp this).resolve_right hs
  rw [hb, hc] at e11 e22 hdet
  have ha0 : M 0 0 ≠ 0 := by
    intro h
    rw [h] at e11
    simp at e11
  have had : M 0 0 = M 1 1 := by
    have : M 0 0 * (M 0 0 - M 1 1) = 0 := by linear_combination e11 - hdet
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha0)
  have ha : (M 0 0 - 1) * (M 0 0 + 1) = 0 := by linear_combination e11
  rcases mul_eq_zero.mp ha with h | h
  · exfalso
    apply hM1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ← had, sub_eq_zero.mp h]
  · have h' : M 0 0 = -1 := eq_neg_of_add_eq_zero_left h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ← had, h']

theorem eq_neg_one_of_finrank_le_two {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (hV : Module.finrank F V ≤ 2)
    {t : V →ₗ[F] V} (ht : t * t = 1) (hdet : LinearMap.det t = 1) (ht1 : t ≠ 1) : t = -1 := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank F V = n := ⟨_, rfl⟩
  let b : Module.Basis (Fin n) F V := Module.finBasisOfFinrankEq F V hn
  set M := LinearMap.toMatrix b b t with hMdef
  have hM : M * M = 1 := by
    rw [hMdef, ← LinearMap.toMatrix_mul, ht, LinearMap.toMatrix_one]
  have hMdet : M.det = 1 := by rw [hMdef, LinearMap.det_toMatrix, hdet]
  have hM1 : M ≠ 1 := fun h => ht1 ((LinearMap.toMatrix b b).injective
    (by rw [← hMdef, h, LinearMap.toMatrix_one]))
  rw [hn] at hV
  have key : M = -1 := by
    interval_cases n
    · exact absurd (Subsingleton.elim M 1) hM1
    · exfalso
      apply hM1
      have e := congrFun (congrFun hM 0) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply_eq] at e
      rw [Matrix.det_fin_one] at hMdet
      ext i j
      fin_cases i; fin_cases j
      simpa using hMdet
    · exact eq_neg_one_of_mul_self_eq_one h2 hM hMdet hM1
  apply (LinearMap.toMatrix b b).injective
  rw [← hMdef, key, map_neg, LinearMap.toMatrix_one]

theorem det_eq_one_of_isPerfect {F V K : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Group K] [Group.IsPerfect K] (ρ : Representation F K V) (k : K) :
    LinearMap.det (ρ k) = 1 := by
  let φ : K →* Fˣ := (Units.map (LinearMap.det : (V →ₗ[F] V) →* F)).comp ρ.asGroupHom
  have hker : commutator K ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [Group.IsPerfect.commutator_eq_top] at hker
  have h := hker (Subgroup.mem_top k)
  rw [MonoidHom.mem_ker] at h
  have h' := congrArg Units.val h
  simpa [φ, Representation.asGroupHom_apply] using h'

theorem rep_eq_one_of_finrank_le_two {F V K : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (hV : Module.finrank F V ≤ 2)
    [Group K] [Group.IsPerfect K] (ρ : Representation F K V)
    (hK : (∃ k, ρ.asGroupHom k ≠ 1) → ∃ a b : K,
      ρ.asGroupHom a * ρ.asGroupHom a = 1 ∧ ρ.asGroupHom b * ρ.asGroupHom b = 1 ∧
      ρ.asGroupHom a * ρ.asGroupHom b = ρ.asGroupHom b * ρ.asGroupHom a ∧
      ρ.asGroupHom a ≠ 1 ∧ ρ.asGroupHom b ≠ 1 ∧ ρ.asGroupHom a ≠ ρ.asGroupHom b) :
    ∀ k, ρ k = 1 := by
  by_contra hne
  push Not at hne
  obtain ⟨k, hk⟩ := hne
  have hk' : ∃ k, ρ.asGroupHom k ≠ 1 := ⟨k, fun h => hk (by
    have := congrArg Units.val h
    rwa [Representation.asGroupHom_apply, Units.val_one] at this)⟩
  obtain ⟨a, b, ha, hb, -, ha1, hb1, hab⟩ := hK hk'
  have hneg : ∀ x : K, ρ.asGroupHom x * ρ.asGroupHom x = 1 → ρ.asGroupHom x ≠ 1 →
      ρ x = -1 := by
    intro x hx hx1
    refine eq_neg_one_of_finrank_le_two h2 hV ?_ (det_eq_one_of_isPerfect ρ x) ?_
    · have := congrArg Units.val hx
      rwa [Units.val_mul, Representation.asGroupHom_apply, Units.val_one] at this
    · intro h
      apply hx1
      apply Units.ext
      rw [Representation.asGroupHom_apply, h, Units.val_one]
  apply hab
  apply Units.ext
  rw [Representation.asGroupHom_apply, Representation.asGroupHom_apply, hneg a ha ha1,
    hneg b hb hb1]

end CFSG.RankThree.PartTwo.Sec20.Res11

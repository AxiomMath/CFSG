module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.Quasithin.QP

open Matrix

variable {F : Type} [Field F]

@[expose] def diag3 (a b : Fˣ) : SpecialLinearGroup (Fin 3) F :=
  ⟨Matrix.diagonal ![(a : F), (b : F), ((a : F) * (b : F))⁻¹], by
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    exact mul_inv_cancel₀ (mul_ne_zero a.ne_zero b.ne_zero)⟩

theorem coe_diag3 (a b : Fˣ) :
    ((diag3 a b : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(a : F), (b : F), ((a : F) * (b : F))⁻¹] := rfl

theorem diag3_mul (a b a' b' : Fˣ) :
    (diag3 a b : SpecialLinearGroup (Fin 3) F) * diag3 a' b' = diag3 (a * a') (b * b') := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_diag3, coe_diag3, coe_diag3, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · simp
  · simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Units.val_mul]
    field_simp

@[expose] def diag3Hom : Fˣ × Fˣ →* SpecialLinearGroup (Fin 3) F where
  toFun p := diag3 p.1 p.2
  map_one' := by
    apply Subtype.ext
    rw [coe_diag3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' p q := (diag3_mul p.1 p.2 q.1 q.2).symm

theorem coe_diag3Hom_apply (p : Fˣ × Fˣ) :
    (diag3Hom p : SpecialLinearGroup (Fin 3) F) = diag3 p.1 p.2 := rfl

theorem exists_not_isCyclic_isPGroup_five [Finite F] (h : 5 ∣ Nat.card F - 1) :
    ∃ E : Subgroup (SpecialLinearGroup (Fin 3) F), IsPGroup 5 E ∧ ¬ IsCyclic E := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fˣ, orderOf ζ = 5 :=
    exists_prime_orderOf_dvd_card' 5 (by rwa [Nat.card_units])
  have hζ5 : ζ ^ 5 = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hζ] at this
  have hζ1 : ζ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hζ
    omega
  set μ : Subgroup Fˣ := (powMonoidHom 5 : Fˣ →* Fˣ).ker with hμ
  have hmem : ∀ a : Fˣ, a ∈ μ ↔ a ^ 5 = 1 := fun a => by
    rw [hμ, MonoidHom.mem_ker, powMonoidHom_apply]
  set E : Subgroup (SpecialLinearGroup (Fin 3) F) := (μ.prod μ).map diag3Hom with hE
  refine ⟨E, ?_, ?_⟩
  · intro g
    obtain ⟨p, hp, hg⟩ := g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hg, ← map_pow]
    have : p ^ 5 = 1 := Prod.ext ((hmem _).1 hp.1) ((hmem _).1 hp.2)
    rw [this, map_one]
  · intro hcyc
    set x : SpecialLinearGroup (Fin 3) F := diag3Hom (ζ, 1) with hx
    set y : SpecialLinearGroup (Fin 3) F := diag3Hom (1, ζ) with hy
    have hxE : x ∈ E := ⟨(ζ, 1), ⟨(hmem ζ).2 hζ5, (hmem 1).2 (one_pow 5)⟩, rfl⟩
    have hyE : y ∈ E := ⟨(1, ζ), ⟨(hmem 1).2 (one_pow 5), (hmem ζ).2 hζ5⟩, rfl⟩
    have hx5 : x ^ 5 = 1 := by
      rw [hx, ← map_pow]
      have : ((ζ, 1) : Fˣ × Fˣ) ^ 5 = 1 := Prod.ext hζ5 (one_pow 5)
      rw [this, map_one]
    have hy5 : y ^ 5 = 1 := by
      rw [hy, ← map_pow]
      have : ((1, ζ) : Fˣ × Fˣ) ^ 5 = 1 := Prod.ext (one_pow 5) hζ5
      rw [this, map_one]
    have hx1 : x ≠ 1 := by
      intro h1
      have := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h1
      simp [hx, coe_diag3Hom_apply, coe_diag3] at this
      exact hζ1 this
    have hy1 : y ≠ 1 := by
      intro h1
      have := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 1 1) h1
      simp [hy, coe_diag3Hom_apply, coe_diag3] at this
      exact hζ1 this
    have hox : orderOf x = 5 := orderOf_eq_prime hx5 hx1
    have hoy : orderOf y = 5 := orderOf_eq_prime hy5 hy1
    set X' : Subgroup ↥E := (Subgroup.zpowers x).subgroupOf E with hX'
    set Y' : Subgroup ↥E := (Subgroup.zpowers y).subgroupOf E with hY'
    have hXle : Subgroup.zpowers x ≤ E := (Subgroup.zpowers_le).2 hxE
    have hYle : Subgroup.zpowers y ≤ E := (Subgroup.zpowers_le).2 hyE
    have hcX : Nat.card X' = 5 := by
      rw [hX', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXle).toEquiv, Nat.card_zpowers, hox]
    have hcY : Nat.card Y' = 5 := by
      rw [hY', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv, Nat.card_zpowers, hoy]
    have hfX : Finite X' := Nat.finite_of_card_ne_zero (by omega)
    have hfY : Finite Y' := Nat.finite_of_card_ne_zero (by omega)
    have heq : X' = Y' := (IsCyclic.subgroup_eq_iff_card_eq).2 (hcX.trans hcY.symm)
    have hyx : y ∈ Subgroup.zpowers x := by
      have : (⟨y, hyE⟩ : ↥E) ∈ Y' := Subgroup.mem_zpowers y
      rw [← heq] at this
      exact this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyx
    have hk' : x ^ k = diag3Hom ((ζ, 1) ^ k) := by rw [hx, ← map_zpow]
    have := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 1 1)
      (hk.symm.trans hk')
    simp [hy, coe_diag3Hom_apply, coe_diag3] at this
    exact hζ1 this

end CFSG.Quasithin.QP

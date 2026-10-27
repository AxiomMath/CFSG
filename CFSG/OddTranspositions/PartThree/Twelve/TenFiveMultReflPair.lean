module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultBridge
public import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix
open scoped commutatorElement

theorem fiveForm_add_add (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (x + y) (x + y) =
      fiveForm k ε x x + 2 * fiveForm k ε x y + fiveForm k ε y y := by
  unfold fiveForm
  simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  have hsum : (∑ i : Fin k, y i.castSucc * x i.castSucc) =
      ∑ i : Fin k, x i.castSucc * y i.castSucc :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hsum]
  ring

theorem isSquare_mul_of_isSquare_iff {x y : ZMod 5} (h : IsSquare x ↔ IsSquare y) :
    IsSquare (x * y) := by
  have hclosed : ∀ x y : ZMod 5, (IsSquare x ↔ IsSquare y) → IsSquare (x * y) := by decide
  exact hclosed x y h

theorem fiveReflOf_mul_self (n : ℕ) (ε : Bool) (x : Fin (n + 1) → ZMod 5) :
    fiveReflOf n ε x * fiveReflOf n ε x = 1 := by
  apply Units.ext
  change fiveReflMatrix n ε x * fiveReflMatrix n ε x = 1
  exact fiveReflMatrix_mul_self n ε x

theorem mul_mem_fiveOmega_of_mem_fiveReflections {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    {ra rb : fiveReflectionGroup k ε π}
    (ha : (ra : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π)
    (hb : (rb : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π) :
    ((ra * rb : fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveOmega k ε := by
  obtain ⟨g, hg, hconj⟩ := isConj_of_mem_fiveReflections hk ε π ha hb
  obtain ⟨a, -, -, haeq⟩ := exists_eq_fiveReflOf ha
  have hra2 : (ra : GL (Fin (k + 1)) (ZMod 5)) * (ra : GL (Fin (k + 1)) (ZMod 5)) = 1 := by
    rw [haeq]
    exact fiveReflOf_mul_self k ε a
  have hinv : (ra : GL (Fin (k + 1)) (ZMod 5))⁻¹ = (ra : GL (Fin (k + 1)) (ZMod 5)) := by
    rw [inv_eq_iff_mul_eq_one]
    exact hra2
  have hkey : ((ra * rb : fiveReflectionGroup k ε π) : GL (Fin (k + 1)) (ZMod 5)) =
      ⁅(ra : GL (Fin (k + 1)) (ZMod 5)), g⁆ := by
    rw [Subgroup.coe_mul, ← hconj, commutatorElement_def, hinv]
    group
  rw [hkey, ← commutator_fiveReflectionGroup_eq_fiveOmega hk ε π]
  exact Subgroup.commutator_mem_commutator ra.2 hg

theorem fiveForm_eq_zero_of_commute_fiveReflOf {k : ℕ} {ε : Bool}
    {a b : Fin (k + 1) → ZMod 5}
    (ha : fiveForm k ε a a ≠ 0) (hb : fiveForm k ε b b ≠ 0)
    (hcomm : fiveReflOf k ε a * fiveReflOf k ε b = fiveReflOf k ε b * fiveReflOf k ε a)
    (hne : fiveReflOf k ε a ≠ fiveReflOf k ε b) :
    fiveForm k ε a b = 0 := by
  by_contra hc
  have h := congrArg (fun g : GL (Fin (k + 1)) (ZMod 5) =>
    (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a) hcomm
  simp only [Units.val_mul] at h
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
  simp only [fiveReflOf_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, fiveForm_comm k ε b a,
    mul_assoc] at h
  field_simp at h
  simp only [smul_sub, sub_smul, smul_smul] at h
  have h1 : (2 * fiveForm k ε a b / fiveForm k ε b b *
        (2 * fiveForm k ε a b / fiveForm k ε a a)) • a =
      (2 * (2 * fiveForm k ε a b / fiveForm k ε b b)) • b := by
    linear_combination (norm := abel) h
  have hX : (2 * fiveForm k ε a b / fiveForm k ε b b) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by decide) hc) hb
  have h2 : (2 * fiveForm k ε a b / fiveForm k ε b b) •
      ((2 * fiveForm k ε a b / fiveForm k ε a a) • a) =
      (2 * fiveForm k ε a b / fiveForm k ε b b) • ((2 : ZMod 5) • b) := by
    rw [smul_smul, smul_smul]
    rw [show 2 * fiveForm k ε a b / fiveForm k ε b b * 2 =
      2 * (2 * fiveForm k ε a b / fiveForm k ε b b) by ring]
    exact h1
  have h3 : (2 * fiveForm k ε a b / fiveForm k ε a a) • a = (2 : ZMod 5) • b :=
    (IsUnit.smul_left_cancel (isUnit_iff_ne_zero.mpr hX)).mp h2
  have hb_eq : b = (fiveForm k ε a b / fiveForm k ε a a) • a := by
    calc b = (1 : ZMod 5) • b := (one_smul _ _).symm
      _ = ((2 : ZMod 5)⁻¹ * 2) • b := by rw [inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0)]
      _ = (2 : ZMod 5)⁻¹ • ((2 : ZMod 5) • b) := (smul_smul _ _ _).symm
      _ = (2 : ZMod 5)⁻¹ • ((2 * fiveForm k ε a b / fiveForm k ε a a) • a) := by rw [← h3]
      _ = ((2 : ZMod 5)⁻¹ * (2 * fiveForm k ε a b / fiveForm k ε a a)) • a := smul_smul _ _ _
      _ = (fiveForm k ε a b / fiveForm k ε a a) • a := by
            congr 1
            field_simp [show (2 : ZMod 5) ≠ 0 from by decide, ha]
  have hcq : fiveForm k ε a b / fiveForm k ε a a ≠ 0 := div_ne_zero hc ha
  have : fiveReflOf k ε b = fiveReflOf k ε a := by
    rw [hb_eq, fiveReflOf_smul k ε a hcq]
  exact hne this.symm

theorem map_fiveReflOf_mulVec {k : ℕ} {ε : Bool} {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q₀ : (ι → ZMod 5) → ZMod 5}
    (S : (Fin (k + 1) → ZMod 5) ≃ₗ[ZMod 5] (ι → ZMod 5)) {ν : ZMod 5} (hν : ν ≠ 0)
    (hS : ∀ v, Q₀ (S v) = ν * fiveForm k ε v v)
    {a : Fin (k + 1) → ZMod 5} (ha : fiveForm k ε a a ≠ 0) (x : Fin (k + 1) → ZMod 5) :
    S (((fiveReflOf k ε a : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x) =
      S x - ((Q₀ (S x + S a) - Q₀ (S x) - Q₀ (S a)) * (Q₀ (S a))⁻¹) • S a := by
  have hcoef : 2 * fiveForm k ε x a * (fiveForm k ε a a)⁻¹ =
      (Q₀ (S x + S a) - Q₀ (S x) - Q₀ (S a)) * (Q₀ (S a))⁻¹ := by
    rw [← map_add, hS (x + a), hS x, hS a, fiveForm_add_add]
    field_simp [hν, ha]
    ring
  rw [fiveReflOf_mulVec, map_sub, map_smul, hcoef]

end CFSG.OddTranspositions.PartThree

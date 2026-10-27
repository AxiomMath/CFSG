module

public import CFSG.OddTranspositions.PartThree.FiveReflection
import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

@[expose] def fiveSignRep (π : Bool) : ZMod 5 := if π then 1 else 2

theorem fiveSignRep_ne_zero (π : Bool) : fiveSignRep π ≠ 0 := by
  cases π <;> decide

theorem isSquare_fiveSignRep_iff (π : Bool) : IsSquare (fiveSignRep π) ↔ π = true := by
  cases π <;> decide

theorem exists_sq_mul_eq_of_isSquare_iff {a c : ZMod 5} (ha : a ≠ 0) (hc : c ≠ 0)
    (h : IsSquare a ↔ IsSquare c) : ∃ l : ZMod 5, l ^ 2 * a = c := by
  revert a c
  decide

theorem fiveForm_add_left (k : ℕ) (ε : Bool) (x x' y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (x + x') y = fiveForm k ε x y + fiveForm k ε x' y := by
  simp only [fiveForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem fiveForm_smul_left (k : ℕ) (ε : Bool) (r : ZMod 5) (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (r • x) y = r * fiveForm k ε x y := by
  simp only [fiveForm, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

@[expose] def fiveBilin (k : ℕ) (ε π : Bool) :
    LinearMap.BilinForm (ZMod 5) (Fin (k + 1) → ZMod 5) :=
  LinearMap.mk₂ (ZMod 5) (fun x y => (fiveSignRep π)⁻¹ * fiveForm k ε x y)
    (fun x x' y => by rw [fiveForm_add_left, mul_add])
    (fun r x y => by rw [fiveForm_smul_left, smul_eq_mul]; ring)
    (fun x y y' => by rw [fiveForm_comm, fiveForm_add_left, fiveForm_comm k ε y,
      fiveForm_comm k ε y', mul_add])
    (fun r x y => by rw [fiveForm_comm, fiveForm_smul_left, fiveForm_comm k ε y, smul_eq_mul]
                     ring)

theorem fiveBilin_apply (k : ℕ) (ε π : Bool) (x y : Fin (k + 1) → ZMod 5) :
    fiveBilin k ε π x y = (fiveSignRep π)⁻¹ * fiveForm k ε x y :=
  rfl

theorem fiveForm_single (k : ℕ) (ε : Bool) (x : Fin (k + 1) → ZMod 5) (i : Fin (k + 1)) :
    fiveForm k ε x (Pi.single i 1) =
      (if i = Fin.last k then -(if ε then 1 else 2) else 1) * x i := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · have hne : (Fin.last k) ≠ j.castSucc := fun h => (Fin.castSucc_lt_last j).ne' h
    simp only [fiveForm, Pi.single_apply, Fin.castSucc_inj, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hne, if_false, sub_zero,
      (Fin.castSucc_lt_last j).ne, one_mul]
  · simp only [fiveForm, Pi.single_apply, mul_one, mul_zero, if_true,
      (fun j : Fin k => (Fin.castSucc_lt_last j).ne), if_false, Finset.sum_const_zero,
      zero_sub, neg_mul]

theorem fiveBilin_comm (k : ℕ) (ε π : Bool) (x y : Fin (k + 1) → ZMod 5) :
    fiveBilin k ε π x y = fiveBilin k ε π y x := by
  rw [fiveBilin_apply, fiveBilin_apply, fiveForm_comm]

theorem five_mul_inv_cancel {a : ZMod 5} (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  revert a
  decide +kernel

theorem five_inv_eq_of_mul_eq_one {a y : ZMod 5} (h : a * y = 1) : a⁻¹ = y := by
  revert a y
  decide +kernel

theorem fiveCoeff_ne_zero (P : Prop) [Decidable P] (ε : Bool) :
    (if P then -(if ε then 1 else 2) else 1 : ZMod 5) ≠ 0 := by
  split_ifs <;> decide

theorem five_eq_zero_of_mul_mul {c e x : ZMod 5} (hc : c ≠ 0) (he : e ≠ 0)
    (h : c * (e * x) = 0) : x = 0 := by
  revert c e x
  decide

theorem fiveBilin_nondegenerate (k : ℕ) (ε π : Bool) (x : Fin (k + 1) → ZMod 5)
    (hx : ∀ y, fiveBilin k ε π x y = 0) : x = 0 := by
  funext i
  have h := hx (Pi.single i 1)
  rw [fiveBilin_apply, fiveForm_single] at h
  have hc : (fiveSignRep π)⁻¹ ≠ 0 := fun h0 => by
    have := five_mul_inv_cancel (fiveSignRep_ne_zero π)
    rw [h0, mul_zero] at this
    exact absurd this (by decide)
  exact five_eq_zero_of_mul_mul hc (fiveCoeff_ne_zero _ ε) h

theorem fischerTransvections_fiveBilin (k : ℕ) (ε π : Bool) :
    CFSG.Open.fischerTransvections (fun x y => -2 * fiveBilin k ε π x y)
        (fun v => fiveBilin k ε π v v = 1) = fiveReflections k ε π := by
  have hc := fiveSignRep_ne_zero π
  have hcc : fiveSignRep π * (fiveSignRep π)⁻¹ = 1 := five_mul_inv_cancel hc
  ext g
  constructor
  · rintro ⟨v, hv, hg⟩
    rw [fiveBilin_apply] at hv
    have hQ : fiveForm k ε v v = fiveSignRep π :=
      calc fiveForm k ε v v = fiveSignRep π * ((fiveSignRep π)⁻¹ * fiveForm k ε v v) := by
            rw [← mul_assoc, hcc, one_mul]
        _ = fiveSignRep π := by rw [hv, mul_one]
    refine ⟨v, by rw [hQ]; exact hc, by rw [hQ]; exact isSquare_fiveSignRep_iff π, fun x => ?_⟩
    rw [hg x]
    beta_reduce
    rw [fiveBilin_apply, hQ, sub_eq_add_neg, ← neg_smul]
    congr 2
    ring
  · rintro ⟨v, hQ, hsq, hg⟩
    obtain ⟨l, hl⟩ := exists_sq_mul_eq_of_isSquare_iff hQ hc
      (hsq.trans (isSquare_fiveSignRep_iff π).symm)
    have hlv : ∀ x, fiveForm k ε x (l • v) = l * fiveForm k ε x v := fun x => by
      rw [fiveForm_comm, fiveForm_smul_left, fiveForm_comm]
    have hinv : (fiveForm k ε v v)⁻¹ = l ^ 2 * (fiveSignRep π)⁻¹ := by
      apply five_inv_eq_of_mul_eq_one
      rw [← mul_assoc, mul_comm _ (l ^ 2), hl, hcc]
    refine ⟨l • v, ?_, fun x => ?_⟩
    · show fiveBilin k ε π (l • v) (l • v) = 1
      rw [fiveBilin_apply, hlv, fiveForm_smul_left]
      calc (fiveSignRep π)⁻¹ * (l * (l * fiveForm k ε v v))
          = (fiveSignRep π)⁻¹ * (l ^ 2 * fiveForm k ε v v) := by ring
        _ = 1 := by rw [hl, mul_comm]; exact hcc
    · rw [hg x]
      beta_reduce
      rw [fiveBilin_apply, hlv, smul_smul, sub_eq_add_neg, ← neg_smul, hinv]
      congr 2
      ring

theorem fischerModel_of_isFiveReflectionModel {X : Type*} [Group X] {E : Set X} {k : ℕ}
    {ε π : Bool} (h : IsFiveReflectionModel k ε π E) :
    ∃ b : LinearMap.BilinForm (ZMod 5) (Fin (k + 1) → ZMod 5),
      (∀ x y, b x y = b y x) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      CFSG.Open.fischerCentralQuotientModel E
        (Subgroup.closure
          (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1))
        (CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1) := by
  refine ⟨fiveBilin k ε π, fiveBilin_comm k ε π, fiveBilin_nondegenerate k ε π, ?_⟩
  rw [fischerTransvections_fiveBilin]
  exact h

end CFSG.OddTranspositions.PartThree

end

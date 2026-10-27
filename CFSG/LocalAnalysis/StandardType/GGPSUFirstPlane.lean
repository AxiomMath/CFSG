module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSADefs
public import CFSG.LieType.Universal.Unitary.Comparison
import CFSG.LocalAnalysis.StandardType.GGPSUFirstPlaneAux

public section

namespace CFSG.StandardType.SelectedRoot

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Phan Matrix

private theorem ggPSUFP_inv_apply {K : Type} [Field K] (σ : K ≃+* K) {n : ℕ}
    (P : GL (Fin n) K)
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) K) * (P : Matrix (Fin n) (Fin n) K) =
      antidiag n) (c j : Fin n) :
    ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) c j =
      σ ((P : Matrix (Fin n) (Fin n) K) j (Fin.rev c)) := by
  have hleft : (antidiag n : Matrix (Fin n) (Fin n) K) * conjTr σ (P : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [Matrix.mul_assoc, hP, antidiag_mul_self]
  have hinv : ((P : Matrix (Fin n) (Fin n) K))⁻¹ =
      (antidiag n : Matrix (Fin n) (Fin n) K) * conjTr σ (P : Matrix (Fin n) (Fin n) K) :=
    Matrix.inv_eq_left_inv hleft
  rw [Matrix.coe_units_inv, hinv, Matrix.mul_apply, Finset.sum_eq_single (Fin.rev c)]
  · rw [antidiag, Matrix.of_apply, if_pos rfl, one_mul]
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply]
  · intro k _ hk
    rw [antidiag, Matrix.of_apply, if_neg hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (Fin.rev c)) h

theorem exists_suBridge_firstPlane {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) :
    ∃ β : SU (unitaryInvolution K p f) n ≃* Su K p f n,
      ∀ g : SU (unitaryInvolution K p f) n,
        (∀ i j : Fin n, ((i ≠ ⟨0, by omega⟩ ∧ i ≠ Fin.rev ⟨0, by omega⟩) ∨
            (j ≠ ⟨0, by omega⟩ ∧ j ≠ Fin.rev ⟨0, by omega⟩)) →
          ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
            (1 : Matrix (Fin n) (Fin n) K) i j) →
        β g ∈ CFSG.StandardType.ggSuPairBlock K p f n ⟨0, by omega⟩ ⟨1, by omega⟩ := by
  obtain ⟨P, hP, hAsupp⟩ :=
    CFSG.StandardType.ggPSUFP_exists_wittMatrix_firstPlane (K := K) (p := p) (f := f) hK hn
  refine ⟨conjEquiv P hP, ?_⟩
  intro g hg
  simp only [CFSG.StandardType.ggSuPairBlock, Set.mem_setOf_eq]
  intro i j hij
  have hcoe : (((conjEquiv P hP g : Su K p f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (P : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h := coe_conjEquiv P hP g
    rw [show ((conjEquiv P hP g : Su K p f n) : GL (Fin n) K) = P * g * P⁻¹ from h,
      Units.val_mul, Units.val_mul]
  rw [hcoe]
  have hE_left : ∀ a c : Fin n, a.val ≠ 0 → a.val ≠ n - 1 →
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
        (1 : Matrix (Fin n) (Fin n) K)) a c = 0 := by
    intro a c ha0 hal
    have hgac : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a c =
        (1 : Matrix (Fin n) (Fin n) K) a c :=
      hg a c (Or.inl ⟨by intro h; exact ha0 (by rw [h]),
        by intro h; exact hal (by rw [h]; simp [Fin.rev])⟩)
    rw [Matrix.sub_apply, hgac, sub_self]
  have hE_right : ∀ a c : Fin n, c.val ≠ 0 → c.val ≠ n - 1 →
      (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
        (1 : Matrix (Fin n) (Fin n) K)) a c = 0 := by
    intro a c hc0 hcl
    have hgac : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a c =
        (1 : Matrix (Fin n) (Fin n) K) a c :=
      hg a c (Or.inr ⟨by intro h; exact hc0 (by rw [h]),
        by intro h; exact hcl (by rw [h]; simp [Fin.rev])⟩)
    rw [Matrix.sub_apply, hgac, sub_self]
  have hPE : ∀ i c : Fin n, 2 ≤ i.val →
      ((P : Matrix (Fin n) (Fin n) K) * (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
        (1 : Matrix (Fin n) (Fin n) K))) i c = 0 := by
    intro i c hi
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a.val = 0 ∨ a.val = n - 1
    · rcases ha with ha | ha
      · rw [hAsupp i a (Or.inl ha) hi, zero_mul]
      · rw [hAsupp i a (Or.inr ha) hi, zero_mul]
    · rw [hE_left a c (fun h => ha (Or.inl h)) (fun h => ha (Or.inr h)), mul_zero]
  have hPEc : ∀ i c : Fin n, c.val ≠ 0 → c.val ≠ n - 1 →
      ((P : Matrix (Fin n) (Fin n) K) * (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
        (1 : Matrix (Fin n) (Fin n) K))) i c = 0 := by
    intro i c hc0 hcl
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    rw [hE_right a c hc0 hcl, mul_zero]
  have hPi : ∀ c j : Fin n, (c.val = 0 ∨ c.val = n - 1) → 2 ≤ j.val →
      ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) c j = 0 := by
    intro c j hc hj
    rw [ggPSUFP_inv_apply (unitaryInvolution K p f) P hP c j]
    have hrev : (Fin.rev c).val = 0 ∨ (Fin.rev c).val = n - 1 := by
      rcases hc with hc | hc
      · right; have hvv := Fin.val_rev c; omega
      · left; have hvv := Fin.val_rev c; omega
    rw [hAsupp j (Fin.rev c) hrev hj, map_zero]
  have hMij : ((P : Matrix (Fin n) (Fin n) K) * (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
        (1 : Matrix (Fin n) (Fin n) K)) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j = 0 := by
    rcases hij with ⟨hi0, hi1⟩ | ⟨hj0, hj1⟩
    · have hi : 2 ≤ i.val := by
        have h0 : i.val ≠ 0 := by intro h; exact hi0 (Fin.ext (by simpa using h))
        have h1 : i.val ≠ 1 := by intro h; exact hi1 (Fin.ext (by simpa using h))
        omega
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro c _
      rw [hPE i c hi, zero_mul]
    · have hj : 2 ≤ j.val := by
        have h0 : j.val ≠ 0 := by intro h; exact hj0 (Fin.ext (by simpa using h))
        have h1 : j.val ≠ 1 := by intro h; exact hj1 (Fin.ext (by simpa using h))
        omega
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : c.val = 0 ∨ c.val = n - 1
      · rw [hPi c j hc hj, mul_zero]
      · rw [hPEc i c (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h)), zero_mul]
  have hPinv : (P : Matrix (Fin n) (Fin n) K) *
      ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdecomp : (P : Matrix (Fin n) (Fin n) K) * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + (P : Matrix (Fin n) (Fin n) K) * (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
        (1 : Matrix (Fin n) (Fin n) K)) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    conv_lhs => rw [show ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        1 + (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
          (1 : Matrix (Fin n) (Fin n) K)) by rw [← add_sub_assoc, add_sub_cancel_left]]
    rw [mul_add, add_mul, Matrix.mul_one, hPinv]
  rw [hdecomp, Matrix.add_apply, hMij, add_zero]

end CFSG.StandardType.SelectedRoot

end

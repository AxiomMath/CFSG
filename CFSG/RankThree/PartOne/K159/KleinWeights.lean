module

public import CFSG.RankThree.PartOne.K159.KleinModel

public section

namespace CFSG.RankThree.PartOne.K159.Klein

open Matrix CFSG.LocalAnalysis

variable {K : Type} [Field K]

@[expose] def kleinIndexPair : Fin 3 ⊕ Fin 3 → Fin 4 × Fin 4 :=
  Sum.elim ![(0, 1), (0, 2), (0, 3)] ![(2, 3), (1, 3), (1, 2)]

theorem cong_diagonal_apply (w : Fin 4 → K) (v : Fin 3 ⊕ Fin 3 → K) (s : Fin 3 ⊕ Fin 3) :
    cong (diagonal w) v s = w (kleinIndexPair s).1 * w (kleinIndexPair s).2 * v s := by
  rw [cong_apply, diagonal_transpose]
  rcases s with i | i <;> fin_cases i <;> simp [coords, kleinIndexPair, alt, antiMat] <;> ring

abbrev TwoPt (K : Type) [Field K] := {p : Fin 4 × Fin 4 // p.1 ≠ p.2} × Kˣ

@[expose] def twoPtEntry (t : TwoPt K) (k : Fin 4) : K :=
  if k = t.1.1.1 then (t.2 : K) else if k = t.1.1.2 then (t.2 : K)⁻¹ else 1

noncomputable def twoPtSL (t : TwoPt K) : Matrix.SpecialLinearGroup (Fin 4) K :=
  Matrix.SpecialLinearGroup.diag2n t.1.2 (t.2 : K) t.2.ne_zero

theorem coe_twoPtSL (t : TwoPt K) :
    (twoPtSL t : Matrix (Fin 4) (Fin 4) K) = diagonal (twoPtEntry t) := by
  rw [twoPtSL, Matrix.SpecialLinearGroup.diag2n_coe]
  rfl

theorem twoPtSL_inv (t : TwoPt K) : (twoPtSL t)⁻¹ = twoPtSL (t.1, t.2⁻¹) := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_twoPtSL, coe_twoPtSL, diagonal_mul_diagonal,
    Matrix.SpecialLinearGroup.coe_one, ← diagonal_one]
  congr 1
  funext k
  simp only [twoPtEntry, Units.val_inv_eq_inv_val, inv_inv]
  split_ifs <;> simp [t.2.ne_zero]

theorem twoPtEntry_inv (t : TwoPt K) (k : Fin 4) :
    twoPtEntry (t.1, t.2⁻¹) k = (twoPtEntry t k)⁻¹ := by
  simp only [twoPtEntry, Units.val_inv_eq_inv_val, inv_inv]
  split_ifs <;> simp

@[expose] def twoPtWt (ν : Fin 4 → ℤ) (t : TwoPt K) : K := (t.2 : K) ^ (ν t.1.1.1 - ν t.1.1.2)

theorem twoPtWt_add (ν μ : Fin 4 → ℤ) (t : TwoPt K) :
    twoPtWt (ν + μ) t = twoPtWt ν t * twoPtWt μ t := by
  simp only [twoPtWt, Pi.add_apply]
  rw [← zpow_add₀ t.2.ne_zero]
  ring_nf

theorem twoPtWt_ne_zero (ν : Fin 4 → ℤ) (t : TwoPt K) : twoPtWt ν t ≠ 0 :=
  zpow_ne_zero _ t.2.ne_zero

theorem twoPtEntry_eq_twoPtWt (t : TwoPt K) (k : Fin 4) :
    twoPtEntry t k = twoPtWt (Pi.single k 1) t := by
  obtain ⟨⟨⟨x, y⟩, hxy⟩, u⟩ := t
  simp only [twoPtEntry, twoPtWt]
  by_cases hkx : k = x
  · subst hkx
    simp [Pi.single_apply, Ne.symm hxy]
  · by_cases hky : k = y
    · subst hky
      simp [Pi.single_apply, hkx, Ne.symm hkx]
    · simp [Pi.single_apply, hkx, hky, Ne.symm hkx, Ne.symm hky]

private theorem eq_one_of_sq_eq_one' [CharP K 2] {a : K} (h : a ^ 2 = 1) : a = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (a - 1) ^ 2 = 0 := by linear_combination h - (a - 1) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)

@[expose] def HasGap (ν : Fin 4 → ℤ) (S : Finset (Fin 4)) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ (ν x - ν y = 1 ∨ ν x - ν y = -1 ∨ ν x - ν y = 2 ∨ ν x - ν y = -2)

instance (ν : Fin 4 → ℤ) (S : Finset (Fin 4)) : Decidable (HasGap ν S) := by
  unfold HasGap
  infer_instance

theorem exists_twoPtWt_ne [CharP K 2] [Finite K] (hK : 4 ≤ Nat.card K) {ν μ : Fin 4 → ℤ}
    {S : Finset (Fin 4)} (h : HasGap (ν - μ) S) :
    ∃ t : TwoPt K, (∀ k ∉ S, twoPtEntry t k = 1) ∧ twoPtWt ν t ≠ twoPtWt μ t := by
  obtain ⟨x, hx, y, hy, hxy, hgap⟩ := h
  obtain ⟨a, ha0, ha1⟩ : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective (fun i : Fin 2 => if i = 0 then (0 : K) else 1) := by
      intro b
      by_cases hb : b = 0
      · exact ⟨0, by simp [hb]⟩
      · exact ⟨1, by simp [hcon b hb]⟩
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    have h2 : Nat.card (Fin 2) = 2 := by simp
    omega
  set u : Kˣ := Units.mk0 a ha0 with hu_def
  have hu' : (u : K) ≠ 1 := ha1
  have hu0 : (u : K) ≠ 0 := ha0
  refine ⟨(⟨(x, y), hxy⟩, u), fun k hk => ?_, fun h1 => ?_⟩
  · have hkx : k ≠ x := fun h => hk (h ▸ hx)
    have hky : k ≠ y := fun h => hk (h ▸ hy)
    simp [twoPtEntry, hkx, hky]
  ·
    have h2 : (u : K) ^ ((ν - μ) x - (ν - μ) y) = 1 := by
      have e : (ν - μ) x - (ν - μ) y = (ν x - ν y) - (μ x - μ y) := by
        simp only [Pi.sub_apply]
        ring
      rw [e, zpow_sub₀ hu0]
      simp only [twoPtWt] at h1
      rw [h1, div_self (zpow_ne_zero _ hu0)]
    rcases hgap with h | h | h | h <;> rw [h] at h2
    · exact hu' (by simpa using h2)
    · exact hu' (by simpa using h2)
    · exact hu' (eq_one_of_sq_eq_one' (by simpa using h2))
    · refine hu' (eq_one_of_sq_eq_one' ?_)
      have : ((u : K) ^ 2)⁻¹ = 1 := by simpa using h2
      simpa using this

theorem map_twoPtSL_smul_single (σ : K →+* K) (t : TwoPt K) (k : Fin 4) :
    Matrix.SpecialLinearGroup.map σ (twoPtSL t) • (Pi.single k 1 : Fin 4 → K) =
      σ (twoPtEntry t k) • Pi.single k 1 := by
  ext j
  simp [Matrix.SpecialLinearGroup.smul_def, coe_twoPtSL, diagonal_map, mulVec_diagonal,
    Pi.single_apply]
  split_ifs with h <;> simp [h]

theorem rho_twoPtSL_single [CharP K 2] (t : TwoPt K) (s : Fin 3 ⊕ Fin 3) :
    rho (twoPtSL t) (Pi.single s 1) =
      (twoPtEntry t (kleinIndexPair s).1 * twoPtEntry t (kleinIndexPair s).2) • Pi.single s 1 := by
  funext s'
  rw [rho_apply, coe_twoPtSL, cong_diagonal_apply]
  by_cases h : s' = s
  · subst h
    simp
  · simp [Pi.single_apply, h]

end CFSG.RankThree.PartOne.K159.Klein

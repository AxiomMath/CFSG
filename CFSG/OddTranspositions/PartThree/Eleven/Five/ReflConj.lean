module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl
import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix
open FiveAux

private def v0 : V5 := ![0, 0, 0, 0, 2]

private lemma fiveQ_add (x y : V5) :
    fiveForm 4 true (x + y) (x + y) =
      fiveForm 4 true x x + 2 * fiveForm 4 true x y + fiveForm 4 true y y := by
  rw [fiveForm_add_left, fiveForm_add_right, fiveForm_add_right,
    fiveForm_comm 4 true y x]
  ring

private lemma fiveQ_sub (x y : V5) :
    fiveForm 4 true (x - y) (x - y) =
      fiveForm 4 true x x - 2 * fiveForm 4 true x y + fiveForm 4 true y y := by
  rw [fiveForm_sub_left, fiveForm_sub_right, fiveForm_sub_right,
    fiveForm_comm 4 true y x]
  ring

private lemma fiveForm_v0_v0 : fiveForm 4 true v0 v0 = 1 := by decide

private lemma fiveForm_v0_left (w : V5) :
    fiveForm 4 true v0 w = -(2 : ZMod 5) * w (Fin.last 4) := by
  simp [v0, fiveForm, Fin.sum_univ_four]

private lemma two_B_add (w : V5) (hw : fiveForm 4 true w w = 1) :
    2 * fiveForm 4 true w (v0 + w) = fiveForm 4 true (v0 + w) (v0 + w) := by
  rw [fiveForm_add_right 4 true w v0 w, fiveForm_comm 4 true w v0, hw,
    fiveQ_add v0 w, fiveForm_v0_v0, hw]
  ring

private lemma two_B_sub (w : V5) (hw : fiveForm 4 true w w = 1) :
    2 * fiveForm 4 true w (v0 - w) = -fiveForm 4 true (v0 - w) (v0 - w) := by
  rw [fiveForm_sub_right 4 true w v0 w, fiveForm_comm 4 true w v0, hw,
    fiveQ_sub v0 w, fiveForm_v0_v0, hw]
  ring

private lemma coeff_add_one (w : V5) (hw : fiveForm 4 true w w = 1)
    (hQ : fiveForm 4 true (v0 + w) (v0 + w) = 1) :
    2 * fiveForm 4 true w (v0 + w) * (fiveForm 4 true (v0 + w) (v0 + w))⁻¹ = 1 := by
  rw [two_B_add w hw, hQ, ZMod.mul_inv_eq_gcd]; decide

private lemma coeff_add_four (w : V5) (hw : fiveForm 4 true w w = 1)
    (hQ : fiveForm 4 true (v0 + w) (v0 + w) = 4) :
    2 * fiveForm 4 true w (v0 + w) * (fiveForm 4 true (v0 + w) (v0 + w))⁻¹ = 1 := by
  rw [two_B_add w hw, hQ, ZMod.mul_inv_eq_gcd]; decide

private lemma coeff_sub_one (w : V5) (hw : fiveForm 4 true w w = 1)
    (hQ : fiveForm 4 true (v0 - w) (v0 - w) = 1) :
    2 * fiveForm 4 true w (v0 - w) * (fiveForm 4 true (v0 - w) (v0 - w))⁻¹ = -1 := by
  rw [two_B_sub w hw, hQ, neg_mul, ZMod.mul_inv_eq_gcd]; decide

private lemma coeff_sub_four (w : V5) (hw : fiveForm 4 true w w = 1)
    (hQ : fiveForm 4 true (v0 - w) (v0 - w) = 4) :
    2 * fiveForm 4 true w (v0 - w) * (fiveForm 4 true (v0 - w) (v0 - w))⁻¹ = -1 := by
  rw [two_B_sub w hw, hQ, neg_mul, ZMod.mul_inv_eq_gcd]; decide

private lemma refl_add (w : V5) (hw : fiveForm 4 true w w = 1)
    (hQ : fiveForm 4 true (v0 + w) (v0 + w) = 1) :
    (fiveReflOf 4 true (v0 + w) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = -v0 := by
  rw [fiveReflOf_mulVec 4 true (v0 + w) w, coeff_add_one w hw hQ, one_smul]
  abel

private lemma refl_sub (w : V5) (hw : fiveForm 4 true w w = 1)
    (hQ : fiveForm 4 true (v0 - w) (v0 - w) = 1) :
    (fiveReflOf 4 true (v0 - w) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = v0 := by
  rw [fiveReflOf_mulVec 4 true (v0 - w) w, coeff_sub_one w hw hQ, neg_one_smul]
  abel

private lemma refl_add_four (w : V5) (hw : fiveForm 4 true w w = 1)
    (hQ : fiveForm 4 true (v0 + w) (v0 + w) = 4) :
    (fiveReflOf 4 true (v0 + w) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = -v0 := by
  rw [fiveReflOf_mulVec 4 true (v0 + w) w, coeff_add_four w hw hQ, one_smul]
  abel

private lemma refl_sub_four (w : V5) (hw : fiveForm 4 true w w = 1)
    (hQ : fiveForm 4 true (v0 - w) (v0 - w) = 4) :
    (fiveReflOf 4 true (v0 - w) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = v0 := by
  rw [fiveReflOf_mulVec 4 true (v0 - w) w, coeff_sub_four w hw hQ, neg_one_smul]
  abel

private lemma fiveQ_add_v0 (w : V5) (hw : fiveForm 4 true w w = 1) :
    fiveForm 4 true (v0 + w) (v0 + w) = 2 + w (Fin.last 4) := by
  rw [fiveQ_add, fiveForm_v0_v0, fiveForm_v0_left, hw]
  have h : -(4 : ZMod 5) = 1 := by decide
  calc 1 + 2 * (-(2) * w (Fin.last 4)) + 1
      = 1 + (-(4 : ZMod 5)) * w (Fin.last 4) + 1 := by ring
    _ = 2 + w (Fin.last 4) := by rw [h]; ring

private lemma fiveQ_sub_v0 (w : V5) (hw : fiveForm 4 true w w = 1) :
    fiveForm 4 true (v0 - w) (v0 - w) = 2 - w (Fin.last 4) := by
  rw [fiveQ_sub, fiveForm_v0_v0, fiveForm_v0_left, hw]
  have h : (4 : ZMod 5) = -1 := by decide
  calc 1 - 2 * (-(2) * w (Fin.last 4)) + 1
      = 1 - (-(4 : ZMod 5)) * w (Fin.last 4) + 1 := by ring
    _ = 2 - w (Fin.last 4) := by rw [h]; ring

private lemma fiveReflOf_mem_group {x : V5} (hx : fiveForm 4 true x x ≠ 0)
    (hsq : IsSquare (fiveForm 4 true x x)) :
    fiveReflOf 4 true x ∈ fiveReflectionGroup 4 true true := by
  apply Subgroup.subset_closure
  exact fiveReflOf_mem hx (by simp [hsq])

private lemma exists_smul_eq_pm_v0_of_ne_zero (w : V5)
    (hw : fiveForm 4 true w w = 1) (h4 : w (Fin.last 4) ≠ 0) :
    ∃ g ∈ fiveReflectionGroup 4 true true,
      (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = v0 ∨
      (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = -v0 := by
  rcases zmod5_ne_zero_cases (w (Fin.last 4)) h4 with h | h | h | h
  · have hQ : fiveForm 4 true (v0 - w) (v0 - w) = 1 := by
      rw [fiveQ_sub_v0 w hw, h]; decide
    exact ⟨fiveReflOf 4 true (v0 - w),
      fiveReflOf_mem_group (by rw [hQ]; decide) (by rw [hQ]; exact ⟨1, by decide⟩),
      Or.inl (refl_sub w hw hQ)⟩
  · have hQ : fiveForm 4 true (v0 + w) (v0 + w) = 4 := by
      rw [fiveQ_add_v0 w hw, h]; decide
    exact ⟨fiveReflOf 4 true (v0 + w),
      fiveReflOf_mem_group (by rw [hQ]; decide) (by rw [hQ]; exact ⟨2, by decide⟩),
      Or.inr (refl_add_four w hw hQ)⟩
  · have hQ : fiveForm 4 true (v0 - w) (v0 - w) = 4 := by
      rw [fiveQ_sub_v0 w hw, h]; decide
    exact ⟨fiveReflOf 4 true (v0 - w),
      fiveReflOf_mem_group (by rw [hQ]; decide) (by rw [hQ]; exact ⟨2, by decide⟩),
      Or.inl (refl_sub_four w hw hQ)⟩
  · have hQ : fiveForm 4 true (v0 + w) (v0 + w) = 1 := by
      rw [fiveQ_add_v0 w hw, h]; decide
    exact ⟨fiveReflOf 4 true (v0 + w),
      fiveReflOf_mem_group (by rw [hQ]; decide) (by rw [hQ]; exact ⟨1, by decide⟩),
      Or.inr (refl_add w hw hQ)⟩

private lemma fiveForm_single_left (w : V5) (k : Fin 4) :
    fiveForm 4 true w (Pi.single k.castSucc (1 : ZMod 5)) = w k.castSucc := by
  rw [fiveForm]
  have hlast : (Pi.single k.castSucc (1 : ZMod 5) : Fin 5 → ZMod 5) (Fin.last 4) = 0 :=
    Pi.single_eq_of_ne (M := fun _ : Fin 5 => ZMod 5)
      (Fin.castSucc_ne_last k).symm (1 : ZMod 5)
  simp only [if_true, one_mul, hlast, mul_zero, sub_zero]
  simp_rw [Pi.single_apply]
  rw [show (∑ i : Fin 4,
        w i.castSucc * (if i.castSucc = k.castSucc then (1 : ZMod 5) else 0))
      = ∑ i : Fin 4, (if i = k then w k.castSucc else 0) by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hik : i = k
    · subst hik; simp
    · have hc : i.castSucc ≠ k.castSucc := fun h => hik (Fin.castSucc_injective 4 h)
      simp [hik, hc]]
  rw [Finset.sum_ite_eq']
  simp

private lemma fiveForm_single_left_last (w : V5) :
    fiveForm 4 true w (Pi.single (Fin.last 4) (1 : ZMod 5)) = -w (Fin.last 4) := by
  simp [fiveForm, Fin.sum_univ_four, Pi.single_eq_same, Pi.single_eq_of_ne,
    Fin.castSucc_ne_last]

private lemma fiveForm_three_single_right (w : V5) (i j : Fin 4)
    (h4 : w (Fin.last 4) = 0) :
    fiveForm 4 true w
      (Pi.single i.castSucc (1 : ZMod 5) + Pi.single j.castSucc 1 + Pi.single (Fin.last 4) 1)
      = w i.castSucc + w j.castSucc := by
  simp only [fiveForm_add_right]
  rw [fiveForm_single_left w i, fiveForm_single_left w j, fiveForm_single_left_last w, h4]
  ring

private lemma fiveQ_three_single (i j : Fin 4) (hij : i ≠ j) :
    fiveForm 4 true
      (Pi.single i.castSucc (1 : ZMod 5) + Pi.single j.castSucc 1 + Pi.single (Fin.last 4) 1)
      (Pi.single i.castSucc 1 + Pi.single j.castSucc 1 + Pi.single (Fin.last 4) 1) = 1 := by
  revert i j
  decide

private lemma exists_pair_sum_ne_zero (w : V5) (h4 : w (Fin.last 4) = 0)
    (hw : fiveForm 4 true w w = 1) :
    ∃ i j : Fin 4, i ≠ j ∧ w i.castSucc + w j.castSucc ≠ 0 := by
  by_contra h
  push Not at h
  have hsum : ∀ i j : Fin 4, i ≠ j → w i.castSucc + w j.castSucc = 0 := h
  have h01 := hsum 0 1 (by decide)
  have h02 := hsum 0 2 (by decide)
  have h12 := hsum 1 2 (by decide)
  have h0 : w (0 : Fin 4).castSucc = 0 := by
    apply zmod5_two_mul_eq_zero
    calc (2 : ZMod 5) * w (0 : Fin 4).castSucc
        = (w (0 : Fin 4).castSucc + w (1 : Fin 4).castSucc)
            + (w (0 : Fin 4).castSucc + w (2 : Fin 4).castSucc)
            - (w (1 : Fin 4).castSucc + w (2 : Fin 4).castSucc) := by ring
      _ = 0 := by rw [h01, h02, h12]; ring
  have h1 : w (1 : Fin 4).castSucc = 0 := by
    apply zmod5_two_mul_eq_zero
    calc (2 : ZMod 5) * w (1 : Fin 4).castSucc
        = (w (1 : Fin 4).castSucc + w (0 : Fin 4).castSucc)
            + (w (1 : Fin 4).castSucc + w (2 : Fin 4).castSucc)
            - (w (0 : Fin 4).castSucc + w (2 : Fin 4).castSucc) := by ring
      _ = 0 := by rw [hsum 1 0 (by decide), h12, h02]; ring
  have h2 : w (2 : Fin 4).castSucc = 0 := by
    apply zmod5_two_mul_eq_zero
    calc (2 : ZMod 5) * w (2 : Fin 4).castSucc
        = (w (2 : Fin 4).castSucc + w (0 : Fin 4).castSucc)
            + (w (2 : Fin 4).castSucc + w (1 : Fin 4).castSucc)
            - (w (0 : Fin 4).castSucc + w (1 : Fin 4).castSucc) := by ring
      _ = 0 := by rw [hsum 2 0 (by decide), hsum 2 1 (by decide), h01]; ring
  have h3 : w (3 : Fin 4).castSucc = 0 := by
    have h03 := hsum 0 3 (by decide)
    rw [h0, zero_add] at h03
    exact h03
  have hwsum : fiveForm 4 true w w = 0 := by
    rw [fiveForm, Fin.sum_univ_four, h0, h1, h2, h3, h4]
    ring
  rw [hwsum] at hw
  exact absurd hw (by decide)

private lemma exists_smul_eq_pm_v0_of_eq_zero (w : V5)
    (hw : fiveForm 4 true w w = 1) (h4 : w (Fin.last 4) = 0) :
    ∃ g ∈ fiveReflectionGroup 4 true true,
      (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = v0 ∨
      (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = -v0 := by
  obtain ⟨i, j, hij, hs⟩ := exists_pair_sum_ne_zero w h4 hw
  let x : V5 := Pi.single i.castSucc (1 : ZMod 5) + Pi.single j.castSucc 1 +
    Pi.single (Fin.last 4) 1
  have hQx : fiveForm 4 true x x = 1 := by
    dsimp only [x]; exact fiveQ_three_single i j hij
  have hBx : fiveForm 4 true w x = w i.castSucc + w j.castSucc := by
    dsimp only [x]; exact fiveForm_three_single_right w i j h4
  let g : GL (Fin 5) (ZMod 5) := fiveReflOf 4 true x
  have hgmem : g ∈ fiveReflectionGroup 4 true true := by
    dsimp only [g]
    exact fiveReflOf_mem_group (by rw [hQx]; decide) (by rw [hQx]; exact ⟨1, by decide⟩)
  have hw'Q : fiveForm 4 true ((g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w)
      ((g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w) = 1 := by
    rw [fiveForm_mulVec_of_mem hgmem w w, hw]
  have hx4 : x (Fin.last 4) = 1 := by
    dsimp only [x]
    simp only [Pi.add_apply, Pi.single_apply]
    rw [if_neg (Fin.castSucc_ne_last i).symm, if_neg (Fin.castSucc_ne_last j).symm]
    simp
  have hw'4 : ((g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w) (Fin.last 4) ≠ 0 := by
    have hval : ((g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w) (Fin.last 4)
        = -(2 : ZMod 5) * (w i.castSucc + w j.castSucc) := by
      rw [show (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w
          = w - (2 * fiveForm 4 true w x * (fiveForm 4 true x x)⁻¹) • x from
        fiveReflOf_mulVec 4 true x w]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h4, hBx, hQx, ZMod.inv_one,
        mul_one, zero_sub, hx4]
      ring
    rw [hval]
    intro hzero
    apply hs
    apply zmod5_two_mul_eq_zero
    rw [neg_mul] at hzero
    exact neg_eq_zero.mp hzero
  obtain ⟨g', hg'mem, hg'⟩ := exists_smul_eq_pm_v0_of_ne_zero _ hw'Q hw'4
  refine ⟨g' * g, mul_mem hg'mem hgmem, ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
  exact hg'

private lemma exists_sq_mul_eq_one {s : ZMod 5} (hs : s ≠ 0) (hsq : IsSquare s) :
    ∃ c : ZMod 5, c ≠ 0 ∧ c ^ 2 * s = 1 := by
  have h : ∀ s : ZMod 5, s ≠ 0 → IsSquare s → ∃ c : ZMod 5, c ≠ 0 ∧ c ^ 2 * s = 1 := by
    decide
  exact h s hs hsq

private lemma exists_smul_eq_pm_v0 (w : V5) (hw : fiveForm 4 true w w = 1) :
    ∃ g ∈ fiveReflectionGroup 4 true true,
      (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = v0 ∨
      (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = -v0 := by
  by_cases h4 : w (Fin.last 4) = 0
  · exact exists_smul_eq_pm_v0_of_eq_zero w hw h4
  · exact exists_smul_eq_pm_v0_of_ne_zero w hw h4

private lemma exists_rescale (r : GL (Fin 5) (ZMod 5))
    (hr : r ∈ fiveReflections 4 true true) :
    ∃ w : V5, fiveForm 4 true w w = 1 ∧ r = fiveReflOf 4 true w := by
  obtain ⟨x, hx0, hxsq, hrx⟩ := exists_eq_fiveReflOf hr
  have hsq : IsSquare (fiveForm 4 true x x) := hxsq.mpr rfl
  obtain ⟨c, hc, hcs⟩ := exists_sq_mul_eq_one hx0 hsq
  refine ⟨c • x, ?_, ?_⟩
  · rw [fiveQ_smul, hcs]
  · rw [hrx, fiveReflOf_smul 4 true x hc]

theorem exists_conj_eq_of_mem_fiveReflections {r r' : GL (Fin 5) (ZMod 5)}
    (hr : r ∈ fiveReflections 4 true true) (hr' : r' ∈ fiveReflections 4 true true) :
    ∃ g ∈ fiveReflectionGroup 4 true true, g * r * g⁻¹ = r' := by
  obtain ⟨w, hw, hrw⟩ := exists_rescale r hr
  obtain ⟨w', hw', hr'w'⟩ := exists_rescale r' hr'
  obtain ⟨g, hgmem, hg⟩ := exists_smul_eq_pm_v0 w hw
  obtain ⟨g', hg'mem, hg'⟩ := exists_smul_eq_pm_v0 w' hw'
  have hgr : g * r * g⁻¹ = fiveReflOf 4 true v0 := by
    rw [hrw, conj_fiveReflOf (fiveForm_mulVec_of_mem hgmem)]
    rcases hg with hg | hg
    · rw [hg]
    · rw [hg, ← neg_one_smul (ZMod 5) v0,
        fiveReflOf_smul 4 true v0 (by decide : (-1 : ZMod 5) ≠ 0)]
  have hg'r : g' * r' * g'⁻¹ = fiveReflOf 4 true v0 := by
    rw [hr'w', conj_fiveReflOf (fiveForm_mulVec_of_mem hg'mem)]
    rcases hg' with hg' | hg'
    · rw [hg']
    · rw [hg', ← neg_one_smul (ZMod 5) v0,
        fiveReflOf_smul 4 true v0 (by decide : (-1 : ZMod 5) ≠ 0)]
  refine ⟨g'⁻¹ * g, mul_mem (inv_mem hg'mem) hgmem, ?_⟩
  calc (g'⁻¹ * g) * r * (g'⁻¹ * g)⁻¹
      = g'⁻¹ * (g * r * g⁻¹) * g' := by group
    _ = g'⁻¹ * (g' * r' * g'⁻¹) * g' := by rw [hgr, hg'r]
    _ = r' := by group

end CFSG.OddTranspositions.PartThree

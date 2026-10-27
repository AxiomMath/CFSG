module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl
import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix
open FiveAux

private def v : V5 := ![1, 1, 0, 0, 0]

private def xP2 : V5 := ![1, 0, 1, 0, 0]

private def xM2 : V5 := ![1, 0, -1, 0, 0]

private def xP3 : V5 := ![1, 0, 0, 1, 0]

private def xM3 : V5 := ![1, 0, 0, -1, 0]

private lemma fiveQ_add (x y : V5) :
    fiveForm 4 true (x + y) (x + y) =
      fiveForm 4 true x x + 2 * fiveForm 4 true x y + fiveForm 4 true y y := by
  rw [fiveForm_add_left, fiveForm_add_right, fiveForm_add_right, fiveForm_comm 4 true y x]
  ring

private lemma fiveQ_sub (x y : V5) :
    fiveForm 4 true (x - y) (x - y) =
      fiveForm 4 true x x - 2 * fiveForm 4 true x y + fiveForm 4 true y y := by
  rw [fiveForm_sub_left, fiveForm_sub_right, fiveForm_sub_right, fiveForm_comm 4 true y x]
  ring

private lemma fiveForm_v_v : fiveForm 4 true v v = 2 := by decide

private lemma zmod5_mul_inv (a : ZMod 5) (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [ZMod.mul_inv_eq_gcd]
  have h : ∀ a : ZMod 5, a ≠ 0 → (Nat.gcd a.val 5 : ZMod 5) = 1 := by decide
  exact h a ha

private lemma isSquare_neg_sq (a : ZMod 5) : IsSquare (-(a ^ 2)) := by
  refine ⟨2 * a, ?_⟩
  have h4 : (4 : ZMod 5) = -1 := by decide
  calc -(a ^ 2) = 4 * a ^ 2 := by rw [h4, neg_one_mul]
    _ = (2 * a) * (2 * a) := by ring

private lemma two_B_sub (w : V5) (hw : fiveForm 4 true w w = 2) :
    2 * fiveForm 4 true w (v - w) = -fiveForm 4 true (v - w) (v - w) := by
  rw [fiveForm_sub_right 4 true w v w, fiveForm_comm 4 true w v, hw,
    fiveQ_sub v w, fiveForm_v_v, hw]
  ring

private lemma two_B_add (w : V5) (hw : fiveForm 4 true w w = 2) :
    2 * fiveForm 4 true w (v + w) = fiveForm 4 true (v + w) (v + w) := by
  rw [fiveForm_add_right 4 true w v w, fiveForm_comm 4 true w v, hw,
    fiveQ_add v w, fiveForm_v_v, hw]
  ring

private lemma coeff_eq_self (w x : V5) (hx : fiveForm 4 true x x = 2) :
    2 * fiveForm 4 true w x * (fiveForm 4 true x x)⁻¹ = fiveForm 4 true w x := by
  rw [hx]
  have h2 : (2 : ZMod 5) * 2⁻¹ = 1 := zmod5_mul_inv 2 (by decide)
  calc 2 * fiveForm 4 true w x * 2⁻¹
      = (2 * 2⁻¹) * fiveForm 4 true w x := by ring
    _ = fiveForm 4 true w x := by rw [h2, one_mul]

private lemma fiveReflOf_mulVec_of_Q_2 (w x : V5) (hx : fiveForm 4 true x x = 2) :
    (fiveReflOf 4 true x : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w =
      w - fiveForm 4 true w x • x := by
  rw [fiveReflOf_mulVec 4 true x w, coeff_eq_self w x hx]

private lemma refl_sub (w : V5) (hw : fiveForm 4 true w w = 2)
    (hQ : fiveForm 4 true (v - w) (v - w) = 2 ∨
      fiveForm 4 true (v - w) (v - w) = 3) :
    (fiveReflOf 4 true (v - w) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = v := by
  have hc : 2 * fiveForm 4 true w (v - w) *
      (fiveForm 4 true (v - w) (v - w))⁻¹ = -1 := by
    rw [two_B_sub w hw, neg_mul]
    rcases hQ with h | h
    · rw [h, zmod5_mul_inv (2 : ZMod 5) (by decide)]
    · rw [h, zmod5_mul_inv (3 : ZMod 5) (by decide)]
  rw [fiveReflOf_mulVec 4 true (v - w) w, hc, neg_one_smul]
  abel

private lemma refl_add (w : V5) (hw : fiveForm 4 true w w = 2)
    (hQ : fiveForm 4 true (v + w) (v + w) = 2 ∨
      fiveForm 4 true (v + w) (v + w) = 3) :
    (fiveReflOf 4 true (v + w) : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = -v := by
  have hc : 2 * fiveForm 4 true w (v + w) *
      (fiveForm 4 true (v + w) (v + w))⁻¹ = 1 := by
    rw [two_B_add w hw]
    rcases hQ with h | h
    · rw [h, zmod5_mul_inv (2 : ZMod 5) (by decide)]
    · rw [h, zmod5_mul_inv (3 : ZMod 5) (by decide)]
  rw [fiveReflOf_mulVec 4 true (v + w) w, hc, one_smul]
  abel

private lemma fiveReflOf_mem_group_neg {x : V5} (hx : fiveForm 4 true x x ≠ 0)
    (hsq : ¬ IsSquare (fiveForm 4 true x x)) :
    fiveReflOf 4 true x ∈ fiveReflectionGroup 4 true false := by
  apply Subgroup.subset_closure
  exact fiveReflOf_mem hx (by simp [hsq])

private lemma zmod5_nonsquare_cases (a : ZMod 5) (ha : a ≠ 0) (hsq : ¬ IsSquare a) :
    a = 2 ∨ a = 3 := by
  have h : ∀ a : ZMod 5, a ≠ 0 → ¬ IsSquare a → a = 2 ∨ a = 3 := by decide
  exact h a ha hsq

private lemma fiveForm_w_xP2 (w : V5) :
    fiveForm 4 true w xP2 = w (0 : Fin 4).castSucc + w (2 : Fin 4).castSucc := by
  simp [fiveForm, xP2, Fin.sum_univ_four]

private lemma fiveForm_w_xM2 (w : V5) :
    fiveForm 4 true w xM2 = w (0 : Fin 4).castSucc - w (2 : Fin 4).castSucc := by
  simp [fiveForm, xM2, Fin.sum_univ_four, sub_eq_add_neg]

private lemma fiveForm_w_xP3 (w : V5) :
    fiveForm 4 true w xP3 = w (0 : Fin 4).castSucc + w (3 : Fin 4).castSucc := by
  simp [fiveForm, xP3, Fin.sum_univ_four]

private lemma fiveForm_w_xM3 (w : V5) :
    fiveForm 4 true w xM3 = w (0 : Fin 4).castSucc - w (3 : Fin 4).castSucc := by
  simp [fiveForm, xM3, Fin.sum_univ_four, sub_eq_add_neg]

private lemma fiveForm_v_eq (w : V5) :
    fiveForm 4 true v w = w (0 : Fin 4).castSucc + w (1 : Fin 4).castSucc := by
  simp [fiveForm, v, Fin.sum_univ_four]

private lemma exists_good_x (w : V5) (hw : fiveForm 4 true w w = 2)
    (hb : fiveForm 4 true v w = 0) :
    ∃ x : V5, fiveForm 4 true x x = 2 ∧ fiveForm 4 true v x = 1 ∧
      fiveForm 4 true w x ≠ 0 := by
  by_cases h1 : fiveForm 4 true w xP2 = 0
  · by_cases h2 : fiveForm 4 true w xM2 = 0
    · by_cases h3 : fiveForm 4 true w xP3 = 0
      · by_cases h4 : fiveForm 4 true w xM3 = 0
        · exfalso
          have h01 : w (0 : Fin 4).castSucc + w (2 : Fin 4).castSucc = 0 := by
            rw [← fiveForm_w_xP2 w]; exact h1
          have h02 : w (0 : Fin 4).castSucc - w (2 : Fin 4).castSucc = 0 := by
            rw [← fiveForm_w_xM2 w]; exact h2
          have h03 : w (0 : Fin 4).castSucc + w (3 : Fin 4).castSucc = 0 := by
            rw [← fiveForm_w_xP3 w]; exact h3
          have h04 : w (0 : Fin 4).castSucc - w (3 : Fin 4).castSucc = 0 := by
            rw [← fiveForm_w_xM3 w]; exact h4
          have hvw : w (0 : Fin 4).castSucc + w (1 : Fin 4).castSucc = 0 := by
            rw [← fiveForm_v_eq w]; exact hb
          have h0 : w (0 : Fin 4).castSucc = 0 := by
            apply zmod5_two_mul_eq_zero
            have e : (2 : ZMod 5) * w (0 : Fin 4).castSucc
                = (w (0 : Fin 4).castSucc + w (2 : Fin 4).castSucc)
                  + (w (0 : Fin 4).castSucc - w (2 : Fin 4).castSucc) := by ring
            rw [e, h01, h02]; ring
          have h2' : w (2 : Fin 4).castSucc = 0 := by
            rw [h0, zero_add] at h01; exact h01
          have h3' : w (3 : Fin 4).castSucc = 0 := by
            rw [h0, zero_add] at h03; exact h03
          have h1' : w (1 : Fin 4).castSucc = 0 := by
            rw [h0, zero_add] at hvw; exact hvw
          have hsq : IsSquare (2 : ZMod 5) := by
            have hQw : fiveForm 4 true w w = -(w (Fin.last 4)) ^ 2 := by
              rw [fiveForm, Fin.sum_univ_four, h0, h1', h2', h3']
              simp
              ring
            rw [hw] at hQw
            rw [hQw]
            exact isSquare_neg_sq (w (Fin.last 4))
          exact absurd hsq (by decide)
        · exact ⟨xM3, by decide, by decide, h4⟩
      · exact ⟨xP3, by decide, by decide, h3⟩
    · exact ⟨xM2, by decide, by decide, h2⟩
  · exact ⟨xP2, by decide, by decide, h1⟩

private lemma exists_smul_eq_pm_v_of_Q_2_of_ne_zero (w : V5)
    (hw : fiveForm 4 true w w = 2) (hb : fiveForm 4 true v w ≠ 0) :
    ∃ g ∈ fiveReflectionGroup 4 true false,
      (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = v ∨
      (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = -v := by
  have hb' : fiveForm 4 true v w = 1 ∨ fiveForm 4 true v w = 2 ∨
      fiveForm 4 true v w = 3 ∨ fiveForm 4 true v w = 4 :=
    zmod5_ne_zero_cases _ hb
  rcases hb' with h | h | h | h
  · have hQ : fiveForm 4 true (v - w) (v - w) = 2 := by
      rw [fiveQ_sub, fiveForm_v_v, h, hw]; decide
    exact ⟨fiveReflOf 4 true (v - w),
      fiveReflOf_mem_group_neg (by rw [hQ]; decide) (by rw [hQ]; decide),
      Or.inl (refl_sub w hw (Or.inl hQ))⟩
  · have hQ : fiveForm 4 true (v + w) (v + w) = 3 := by
      rw [fiveQ_add, fiveForm_v_v, h, hw]; decide
    exact ⟨fiveReflOf 4 true (v + w),
      fiveReflOf_mem_group_neg (by rw [hQ]; decide) (by rw [hQ]; decide),
      Or.inr (refl_add w hw (Or.inr hQ))⟩
  · have hQ : fiveForm 4 true (v - w) (v - w) = 3 := by
      rw [fiveQ_sub, fiveForm_v_v, h, hw]; decide
    exact ⟨fiveReflOf 4 true (v - w),
      fiveReflOf_mem_group_neg (by rw [hQ]; decide) (by rw [hQ]; decide),
      Or.inl (refl_sub w hw (Or.inr hQ))⟩
  · have hQ : fiveForm 4 true (v + w) (v + w) = 2 := by
      rw [fiveQ_add, fiveForm_v_v, h, hw]; decide
    exact ⟨fiveReflOf 4 true (v + w),
      fiveReflOf_mem_group_neg (by rw [hQ]; decide) (by rw [hQ]; decide),
      Or.inr (refl_add w hw (Or.inl hQ))⟩

private lemma exists_smul_eq_pm_v_of_Q_2_of_eq_zero (w : V5)
    (hw : fiveForm 4 true w w = 2) (hb : fiveForm 4 true v w = 0) :
    ∃ g ∈ fiveReflectionGroup 4 true false,
      (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = v ∨
      (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = -v := by
  obtain ⟨x, hxQ, hvx, hwx⟩ := exists_good_x w hw hb
  let g0 : GL (Fin 5) (ZMod 5) := fiveReflOf 4 true x
  have hg0mem : g0 ∈ fiveReflectionGroup 4 true false := by
    dsimp only [g0]
    exact fiveReflOf_mem_group_neg (by rw [hxQ]; decide) (by rw [hxQ]; decide)
  have hw'Q : fiveForm 4 true ((g0 : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w)
      ((g0 : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w) = 2 := by
    rw [fiveForm_mulVec_of_mem hg0mem w w, hw]
  have hb' : fiveForm 4 true v ((g0 : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w) ≠ 0 := by
    rw [show (g0 : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w
        = w - fiveForm 4 true w x • x from fiveReflOf_mulVec_of_Q_2 w x hxQ,
      fiveForm_sub_right, fiveForm_smul_right, hvx, mul_one, hb, zero_sub]
    exact neg_ne_zero.mpr hwx
  obtain ⟨g1, hg1mem, hg1⟩ :=
    exists_smul_eq_pm_v_of_Q_2_of_ne_zero _ hw'Q hb'
  refine ⟨g1 * g0, mul_mem hg1mem hg0mem, ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
  exact hg1

private lemma exists_smul_eq_pm_v_of_Q_2 (w : V5) (hw : fiveForm 4 true w w = 2) :
    ∃ g ∈ fiveReflectionGroup 4 true false,
      (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = v ∨
      (g : Matrix (Fin 5) (Fin 5) (ZMod 5)) *ᵥ w = -v := by
  by_cases hb : fiveForm 4 true v w = 0
  · exact exists_smul_eq_pm_v_of_Q_2_of_eq_zero w hw hb
  · exact exists_smul_eq_pm_v_of_Q_2_of_ne_zero w hw hb

private lemma exists_rescale (r : GL (Fin 5) (ZMod 5))
    (hr : r ∈ fiveReflections 4 true false) :
    ∃ w : V5, fiveForm 4 true w w = 2 ∧ r = fiveReflOf 4 true w := by
  obtain ⟨x, hx0, hxsq, hrx⟩ := exists_eq_fiveReflOf hr
  have hsq : ¬ IsSquare (fiveForm 4 true x x) := by simpa using hxsq
  rcases zmod5_nonsquare_cases (fiveForm 4 true x x) hx0 hsq with h | h
  · exact ⟨x, h, hrx⟩
  · refine ⟨(2 : ZMod 5) • x, ?_, ?_⟩
    · rw [fiveQ_smul, h]; decide
    · rw [hrx, fiveReflOf_smul 4 true x (by decide : (2 : ZMod 5) ≠ 0)]

theorem exists_conj_eq_of_mem_fiveReflections_four_true_false {r r' : GL (Fin 5) (ZMod 5)}
    (hr : r ∈ fiveReflections 4 true false) (hr' : r' ∈ fiveReflections 4 true false) :
    ∃ g ∈ fiveReflectionGroup 4 true false, g * r * g⁻¹ = r' := by
  obtain ⟨w, hw, hrw⟩ := exists_rescale r hr
  obtain ⟨w', hw', hr'w'⟩ := exists_rescale r' hr'
  obtain ⟨g, hgmem, hg⟩ := exists_smul_eq_pm_v_of_Q_2 w hw
  obtain ⟨g', hg'mem, hg'⟩ := exists_smul_eq_pm_v_of_Q_2 w' hw'
  have hgr : g * r * g⁻¹ = fiveReflOf 4 true v := by
    rw [hrw, conj_fiveReflOf (fiveForm_mulVec_of_mem hgmem)]
    rcases hg with hg | hg
    · rw [hg]
    · rw [hg, ← neg_one_smul (ZMod 5) v,
        fiveReflOf_smul 4 true v (by decide : (-1 : ZMod 5) ≠ 0)]
  have hg'r : g' * r' * g'⁻¹ = fiveReflOf 4 true v := by
    rw [hr'w', conj_fiveReflOf (fiveForm_mulVec_of_mem hg'mem)]
    rcases hg' with hg' | hg'
    · rw [hg']
    · rw [hg', ← neg_one_smul (ZMod 5) v,
        fiveReflOf_smul 4 true v (by decide : (-1 : ZMod 5) ≠ 0)]
  refine ⟨g'⁻¹ * g, mul_mem (inv_mem hg'mem) hgmem, ?_⟩
  calc (g'⁻¹ * g) * r * (g'⁻¹ * g)⁻¹
      = g'⁻¹ * (g * r * g⁻¹) * g' := by group
    _ = g'⁻¹ * (g' * r' * g'⁻¹) * g' := by rw [hgr, hg'r]
    _ = r' := by group

end CFSG.OddTranspositions.PartThree

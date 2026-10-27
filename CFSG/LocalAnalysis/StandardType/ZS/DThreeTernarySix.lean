module

public import CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs
public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
import all CFSG.LocalAnalysis.StandardType.GGZSHallSoicherInputs
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryChain
public import CFSG.Fischer.Pairs
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

local instance (priority := high) zt6_zmodThreeAddCommGroup : AddCommGroup (ZMod 3) :=
  Ring.toAddCommGroup

private def zt6_codes : Fin 6 → ℕ := ![243, 360, 81, 147, 3, 67]

private def zt6_vec (i : Fin 6) : Fin 6 → ZMod 3 := ternaryDecode 6 (zt6_codes i)

private noncomputable def zt6_r (i : Fin 6) : R3 (diagF3 6 1) :=
  reflBar (diagF3 6 1) (zt6_vec i)

private theorem zt6_norm (i : Fin 6) : diagF3 6 1 (zt6_vec i) (zt6_vec i) = 1 := by
  fin_cases i <;> rw [diagF3_eq_diagDot] <;> decide +kernel

private theorem zt6_exp : ∀ i j : Fin 6, i ≠ j →
    kSixExp i j = if diagDot 6 1 (zt6_vec i) (zt6_vec j) = 0 then 2 else 3 := by
  decide +kernel

private theorem zt6_pair_pow (i j : Fin 6) :
    (zt6_r i * zt6_r j) ^ kSixExp i j = 1 := by
  by_cases hij : i = j
  · rw [hij]
    have hdiag : kSixExp j j = 1 := by fin_cases j <;> decide
    rw [hdiag, pow_one]
    exact reflBar_mul_self (f := diagF3 6 1) (zt6_vec j)
  · have hif : (if diagDot 6 1 (zt6_vec i) (zt6_vec j) = 0 then 2 else 3) =
        (if diagF3 6 1 (zt6_vec i) (zt6_vec j) = 0 then 2 else 3) := by
      rw [diagF3_eq_diagDot]
    rw [zt6_exp i j hij, hif]
    exact reflBar_mul_reflBar_pow_eq_one (isF3Form_diagF3 (by decide)) (zt6_norm i) (zt6_norm j)

private def zt6_w : Fin 6 → ZMod 3 := ![0, 0, 1, 1, 2, 1]

private theorem zt6_w_norm : diagF3 6 1 zt6_w zt6_w = 1 := by
  rw [diagF3_eq_diagDot]
  decide +kernel

private theorem zt6_w3_ne_zero : diagF3 6 1 zt6_w (zt6_vec 3) ≠ 0 := by
  rw [diagF3_eq_diagDot]
  decide +kernel

private theorem zt6_conj_form :
    zt6_vec 1 + diagF3 6 1 (zt6_vec 1) (zt6_vec 2) • zt6_vec 2 = zt6_w := by
  rw [diagF3_eq_diagDot]
  decide +kernel

private theorem zt6_extra : (zt6_r 2 * zt6_r 1 * zt6_r 2 * zt6_r 3) ^ 3 = 1 := by
  have hf : IsF3Form (diagF3 6 1) := isF3Form_diagF3 (by decide)
  have hconj : zt6_r 2 * zt6_r 1 * zt6_r 2 = reflBar (diagF3 6 1) zt6_w := by
    dsimp only [zt6_r]
    rw [reflBar_conj hf, F3.act_refl (zt6_norm 2), zt6_conj_form]
  rw [hconj]
  dsimp only [zt6_r]
  exact reflBar_mul_pow_three hf zt6_w_norm (zt6_norm 3) zt6_w3_ne_zero

private def zt6_triA : Fin 6 → ZMod 3 := ![0, 0, 0, 0, 0, 1]

private def zt6_triB : Fin 6 → ZMod 3 := ![0, 0, 1, 1, 1, 1]

private def zt6_triC : Fin 6 → ZMod 3 := ![0, 1, 0, 1, 2, 1]

private def zt6_triA' : Fin 6 → ZMod 3 := ![1, 0, 0, 0, 0, 0]

private def zt6_triB' : Fin 6 → ZMod 3 := ![1, 0, 1, 1, 1, 0]

private def zt6_triC' : Fin 6 → ZMod 3 := ![1, 1, 0, 1, 2, 0]

private theorem zt6_triA_forms :
    diagF3 6 1 zt6_triA zt6_triA = 1 ∧ diagF3 6 1 zt6_triB zt6_triB = 1 ∧
      diagF3 6 1 zt6_triC zt6_triC = 1 ∧ diagF3 6 1 zt6_triA zt6_triB ≠ 0 ∧
      diagF3 6 1 zt6_triA zt6_triC ≠ 0 ∧ diagF3 6 1 zt6_triB zt6_triC ≠ 0 ∧
      (zt6_triB ≠ zt6_triA ∧ zt6_triB ≠ -zt6_triA) ∧
      (zt6_triC ≠ zt6_triA ∧ zt6_triC ≠ -zt6_triA) ∧
      (zt6_triC ≠ zt6_triB ∧ zt6_triC ≠ -zt6_triB) ∧
      diagF3 6 1 (zt6_triA + diagF3 6 1 zt6_triA zt6_triC • zt6_triC) zt6_triB ≠ 0 ∧
      (zt6_triB ≠ zt6_triA + diagF3 6 1 zt6_triA zt6_triC • zt6_triC ∧
        zt6_triB ≠ -(zt6_triA + diagF3 6 1 zt6_triA zt6_triC • zt6_triC)) := by
  simp only [diagF3_eq_diagDot]
  decide +kernel

private theorem zt6_triA'_forms :
    diagF3 6 1 zt6_triA' zt6_triA' = 1 ∧ diagF3 6 1 zt6_triB' zt6_triB' = 1 ∧
      diagF3 6 1 zt6_triC' zt6_triC' = 1 ∧ diagF3 6 1 zt6_triA' zt6_triB' ≠ 0 ∧
      diagF3 6 1 zt6_triA' zt6_triC' ≠ 0 ∧ diagF3 6 1 zt6_triB' zt6_triC' ≠ 0 ∧
      (zt6_triB' ≠ zt6_triA' ∧ zt6_triB' ≠ -zt6_triA') ∧
      (zt6_triC' ≠ zt6_triA' ∧ zt6_triC' ≠ -zt6_triA') ∧
      (zt6_triC' ≠ zt6_triB' ∧ zt6_triC' ≠ -zt6_triB') ∧
      diagF3 6 1 (zt6_triA' + diagF3 6 1 zt6_triA' zt6_triC' • zt6_triC') zt6_triB' ≠ 0 ∧
      (zt6_triB' ≠ zt6_triA' + diagF3 6 1 zt6_triA' zt6_triC' • zt6_triC' ∧
        zt6_triB' ≠ -(zt6_triA' + diagF3 6 1 zt6_triA' zt6_triC' • zt6_triC')) := by
  simp only [diagF3_eq_diagDot]
  decide +kernel

private theorem zt6_affineTriangle_A :
    AffineTriangle (D3 (diagF3 6 1)) (reflBar (diagF3 6 1) zt6_triA)
      (reflBar (diagF3 6 1) zt6_triB) (reflBar (diagF3 6 1) zt6_triC) := by
  obtain ⟨ha, hb, hc, hab, hac, hbc, hab', hac', hbc', hd, hdb⟩ := zt6_triA_forms
  exact affineTriangle_reflBar (isF3Form_diagF3 (by decide)) (by norm_num)
    ha hb hc hab hac hbc hab' hac' hbc' hd hdb

private theorem zt6_affineTriangle_B :
    AffineTriangle (D3 (diagF3 6 1)) (reflBar (diagF3 6 1) zt6_triA')
      (reflBar (diagF3 6 1) zt6_triB') (reflBar (diagF3 6 1) zt6_triC') := by
  obtain ⟨ha, hb, hc, hab, hac, hbc, hab', hac', hbc', hd, hdb⟩ := zt6_triA'_forms
  exact affineTriangle_reflBar (isF3Form_diagF3 (by decide)) (by norm_num)
    ha hb hc hab hac hbc hab' hac' hbc' hd hdb

private theorem zt6_tri_norm :
    ∀ x ∈ [zt6_triA, zt6_triB, zt6_triC], diagF3 6 1 x x = 1 := by
  simp only [diagF3_eq_diagDot]
  decide +kernel

private theorem zt6_tri_norm' :
    ∀ y ∈ [zt6_triA', zt6_triB', zt6_triC'], diagF3 6 1 y y = 1 := by
  simp only [diagF3_eq_diagDot]
  decide +kernel

private theorem zt6_cross_forms :
    ∀ x ∈ [zt6_triA, zt6_triB, zt6_triC],
      ∀ y ∈ [zt6_triA', zt6_triB', zt6_triC'], diagF3 6 1 x y = 0 := by
  simp only [diagF3_eq_diagDot]
  decide +kernel

private theorem zt6_commute_cross (x y : Fin 6 → ZMod 3)
    (hx : x ∈ [zt6_triA, zt6_triB, zt6_triC])
    (hy : y ∈ [zt6_triA', zt6_triB', zt6_triC']) :
    Commute (reflBar (diagF3 6 1) x) (reflBar (diagF3 6 1) y) :=
  (reflBar_commute_iff (isF3Form_diagF3 (by decide)) (by norm_num)
    (zt6_tri_norm x hx) (zt6_tri_norm' y hy)).2
    (Or.inl (zt6_cross_forms x hx y hy))

private def zt6_init : List ℕ := [243, 360, 81, 147, 3, 67]

private theorem zt6_init_spec : ∀ k ∈ zt6_init, ∃ i : Fin 6, zt6_codes i = k := by
  decide +kernel

private def zt6_steps : List (ℕ × ℕ) :=
  [(243, 243), (243, 360), (360, 360), (360, 81), (360, 147), (81, 81), (81, 147), (81, 603),
   (81, 426), (147, 147), (147, 3), (147, 603), (147, 441), (147, 684), (147, 663), (3, 3),
   (3, 67), (3, 426), (3, 228), (3, 663), (3, 669), (3, 678), (3, 435), (3, 465), (67, 67),
   (67, 150), (67, 429), (67, 231), (67, 348), (67, 672), (67, 681), (67, 438), (67, 600),
   (243, 684), (243, 663), (243, 669), (243, 678), (243, 465), (243, 348), (243, 672),
   (243, 681), (243, 600), (243, 379), (243, 703), (243, 658), (243, 577), (360, 435),
   (360, 429), (360, 231), (360, 681), (360, 438), (360, 460), (360, 208), (360, 658),
   (360, 415), (360, 588), (360, 591), (360, 622), (81, 684), (81, 669), (81, 672), (81, 703),
   (147, 348), (147, 600), (147, 127), (147, 379), (147, 577), (147, 591), (147, 705),
   (147, 622), (147, 668), (147, 555), (147, 532), (147, 534), (147, 551), (3, 231), (3, 672),
   (3, 681), (3, 708), (3, 555), (3, 537), (3, 500), (3, 302), (3, 257), (3, 545), (3, 571),
   (3, 328), (67, 208), (67, 703), (67, 658), (67, 705), (67, 532), (67, 534), (67, 564),
   (67, 285), (67, 321), (67, 528), (67, 571), (67, 328), (486, 441), (486, 465), (486, 460),
   (486, 415), (486, 588), (486, 552), (486, 551), (486, 285), (486, 321), (486, 328),
   (486, 305), (486, 260), (486, 331), (603, 564), (603, 285), (603, 500), (603, 302),
   (603, 612), (603, 571), (603, 503), (603, 305), (603, 574), (720, 228), (720, 577),
   (720, 321), (720, 528), (720, 257), (720, 545), (720, 369), (720, 328), (720, 260),
   (720, 548), (720, 331), (720, 156), (720, 44), (720, 112), (720, 41), (441, 321), (441, 528),
   (441, 257), (441, 545), (441, 612), (441, 571), (441, 260), (441, 548), (441, 574), (441, 18),
   (441, 44), (441, 41), (426, 260), (426, 548), (426, 331), (426, 240), (426, 176), (426, 193),
   (426, 179), (426, 43), (426, 412), (162, 369), (162, 328), (162, 574), (162, 331), (162, 156),
   (162, 159), (162, 115), (162, 95), (162, 112), (162, 98), (162, 178), (162, 236), (162, 107),
   (162, 433), (162, 586), (228, 555), (228, 532), (228, 574), (228, 331), (228, 159), (228, 95),
   (228, 112), (228, 98), (228, 41), (228, 43), (228, 178), (228, 236), (228, 586), (228, 352),
   (684, 41), (684, 240), (684, 179), (684, 178), (684, 236), (684, 107), (684, 433), (684, 586),
   (684, 550), (684, 307), (684, 119), (684, 142), (684, 197), (663, 260), (663, 548),
   (663, 112), (663, 98), (663, 43), (663, 154), (663, 113), (663, 521), (663, 424), (213, 112),
   (213, 98), (213, 41), (213, 43), (213, 412), (213, 433), (213, 329), (213, 335), (213, 544),
   (213, 128), (213, 499), (150, 196), (150, 179), (150, 259), (150, 94), (150, 518), (150, 128),
   (150, 424), (150, 502), (669, 329), (669, 352), (669, 544), (669, 256), (669, 559),
   (678, 548), (678, 574), (678, 433), (678, 461), (678, 71), (435, 98), (435, 412), (435, 97),
   (435, 155), (465, 193), (465, 179), (6, 71), (70, 71), (53, 52)]

private theorem zt6_chainOK : chainOK (diagNext 6 1) (diagOk 6 1) zt6_init zt6_steps = true := by
  decide +kernel

private theorem zt6_cover : ∀ k < 3 ^ 6,
    diagDot 6 1 (ternaryDecode 6 k) (ternaryDecode 6 k) = 1 →
      k ∈ chainLabels (diagNext 6 1) zt6_init zt6_steps := by
  decide +kernel

theorem exists_hsSixRel_D3_diagF3_six_one :
    ∃ r : Fin 6 → R3 (diagF3 6 1), (∀ i, r i ∈ D3 (diagF3 6 1)) ∧ HSSixRel r ∧
      Subgroup.closure (Set.range r) = ⊤ := by
  refine ⟨zt6_r, fun i => reflBar_mem_D3 (zt6_norm i), ?_, ?_⟩
  · change (∀ i j, (zt6_r i * zt6_r j) ^ kSixExp i j = 1) ∧
      (zt6_r 2 * zt6_r 1 * zt6_r 2 * zt6_r 3) ^ 3 = 1
    exact ⟨fun i j => zt6_pair_pow i j, zt6_extra⟩
  let H : Subgroup (R3 (diagF3 6 1)) := Subgroup.closure (Set.range zt6_r)
  have hinit : ∀ k ∈ zt6_init, reflBar (diagF3 6 1) (ternaryDecode 6 k) ∈ H := by
    intro k hk
    obtain ⟨i, hi⟩ := zt6_init_spec k hk
    rw [← hi]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  exact eq_top_of_diagChain (m := 6) (δ := 1) (by norm_num) one_ne_zero
    (H := H) (init := zt6_init) (steps := zt6_steps) hinit zt6_chainOK zt6_cover

theorem exists_frame_D3_diagF3_six_one :
    ∃ d : Fin 6 → R3 (diagF3 6 1), (∀ i, d i ∈ D3 (diagF3 6 1)) ∧ Function.Injective d ∧
      (Pairwise fun i j => Commute (d i) (d j)) ∧ (List.ofFn d).prod = 1 :=
  ⟨fun i => reflBar (diagF3 6 1) (Pi.single i 1), frame_reflBar_diagF3_one (by norm_num)⟩

theorem exists_affineTriangle_pair_D3_diagF3_six_one :
    ∃ a b c a' b' c' : R3 (diagF3 6 1), AffineTriangle (D3 (diagF3 6 1)) a b c ∧
      AffineTriangle (D3 (diagF3 6 1)) a' b' c' ∧
        ∀ x ∈ [a, b, c], ∀ y ∈ [a', b', c'], Commute x y := by
  refine ⟨reflBar (diagF3 6 1) zt6_triA, reflBar (diagF3 6 1) zt6_triB,
    reflBar (diagF3 6 1) zt6_triC, reflBar (diagF3 6 1) zt6_triA',
    reflBar (diagF3 6 1) zt6_triB', reflBar (diagF3 6 1) zt6_triC',
    zt6_affineTriangle_A, zt6_affineTriangle_B, ?_⟩
  intro x hx y hy
  have hx' : x = reflBar (diagF3 6 1) zt6_triA ∨
      x = reflBar (diagF3 6 1) zt6_triB ∨ x = reflBar (diagF3 6 1) zt6_triC := by
    simpa using hx
  have hy' : y = reflBar (diagF3 6 1) zt6_triA' ∨
      y = reflBar (diagF3 6 1) zt6_triB' ∨ y = reflBar (diagF3 6 1) zt6_triC' := by
    simpa using hy
  rcases hx' with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;>
    apply zt6_commute_cross <;> simp

end CFSG.StandardType.ZS

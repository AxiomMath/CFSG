module

public import CFSG.Sporadic.J4.QT2ASyl
public import CFSG.Sporadic.J4.QTOutNorm

public section

namespace CFSG.Sporadic.J4.QT2A

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix

namespace BoundT

theorem el5_eq_wordProd_xJ {w : List ℤ} (hw : ∀ ℓ ∈ w, ℓ ∈ letters) :
    el5 w = wordProd xJ w := by
  unfold el5 wordProd
  congr 1
  refine List.map_congr_left fun l hl => ?_
  rcases letters_cases (hw l hl) with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gen5]

theorem el5_mem_Hj {w : List ℤ} (hw : ∀ ℓ ∈ w, ℓ ∈ letters) : el5 w ∈ Hj := by
  rw [el5_eq_wordProd_xJ hw]
  exact wordProd_mem_Hj hw

theorem chkLoc_parts : (∀ l ∈ aDw, l ∈ letters) ∧ ∀ l ∈ bDw, l ∈ letters := by
  have h := chkLoc_true
  unfold chkLoc at h
  simpa only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] using h

theorem Ycl_le_Hj : Ycl ≤ Hj := by
  rw [Ycl, Subgroup.closure_le]
  obtain ⟨ha, hb⟩ := chkLoc_parts
  rintro _ (rfl | rfl)
  · exact el5_mem_Hj ha
  · exact el5_mem_Hj hb

theorem chkE_parts {n : ℕ} (hn : n < 27) (hn0 : n ≠ 0) :
    (∀ t < 64, wfR (conjE (combMask (eMasks.getD n []) t) (yEl n)) = true) ∧
      allDistinct ((List.range 64).map fun t =>
        conjE (combMask (eMasks.getD n []) t) (yEl n)) = true := by
  have h := chkE_true
  unfold chkE at h
  have h1 := List.all_eq_true.1 h n (List.mem_range.2 hn)
  rcases Bool.or_eq_true_iff.1 h1 with h2 | h2
  · exact absurd (beq_iff_eq.1 h2) hn0
  · unfold eConjOK at h2
    simp only [Bool.and_eq_true] at h2
    obtain ⟨⟨-, h3⟩, h4⟩ := h2
    refine ⟨fun t ht => ?_, h4⟩
    exact List.all_eq_true.1 h3 _ (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩)

section Conj

variable (hM : MatFacts)
include hM

theorem Mx_conj_eta (c n : ℕ) :
    Mx (eta uJ 11 c * yJ n * (eta uJ 11 c)⁻¹) = rowsMatrix (conjE c (yEl n)) := by
  rw [inv_eq_of_mul_eq_one_right (eta_sq (elem_uJ hM) c), map_mul, map_mul,
    Mx_eta hM 11 le_rfl c, Mx_yJ hM n]
  simp only [conjE, etaE, rowsMatrix_mulRows]

theorem hconj : ∀ y ∈ Ycl, y ≠ 1 → ∃ conj : Fin 64 → J, (∀ j, conj j ∈ Eg uJ 11) ∧
    Function.Injective fun j => conj j * y * (conj j)⁻¹ := by
  intro y hy hy1
  obtain ⟨n, hn, rfl⟩ := Ycl_subset hM hy
  have hn27 : n < 27 := hn
  have hn0 : n ≠ 0 := fun h => hy1 (by rw [h, yJ_zero])
  obtain ⟨hw, hd⟩ := chkE_parts hn27 hn0
  refine ⟨fun t => eta uJ 11 (combMask (eMasks.getD n []) t), fun t => eta_mem_Eg 11 le_rfl _, ?_⟩
  intro i j hij
  by_contra hne
  have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
  have hd' := allDistinct_spec hd i j (by simp) (by simp) hne'
  simp only [List.getElem_map, List.getElem_range] at hd'
  apply ne_of_eqRows_false (hw i i.2) (hw j j.2) hd'
  rw [← Mx_conj_eta hM, ← Mx_conj_eta hM]
  exact congrArg Mx hij

end Conj

end BoundT

open BoundT in
theorem card_le_T (hF : J4Facts) {S : Subgroup J} (hS : IsPGroup 2 S) (hSH : S ≤ Hj) {y : J}
    (hyH : y ∈ Hj) (hy3 : orderOf y = 3) (hSy : ∀ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers y) :
    Nat.card S ≤ 2 ^ 15 := by
  have hM := hF.mat
  exact card_le_of_sylow_data Hj (Eg uJ 11) Ycl Ycl_le_Hj Eg_le_Hj (Hj_normalizes_Eg hM)
    (isPGroup_Eg (elem_uJ hM)) (card_Ycl hM) (k := 18570280960)
    (by rw [card_Hj hF]) (by norm_num) (m := 239085)
    (by rw [card_Hj hF]; norm_num) (by norm_num) (hconj hM) hS hSH hyH hy3 hSy

end CFSG.Sporadic.J4.QT2A

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.StandardType.RCKK1IIISU

@[expose] def s5q (v : Fin 4 → ZMod 2) : ZMod 2 :=
  v 0 * v 3 + (v 1 * v 1 + v 1 * v 2 + v 2 * v 2)

@[expose] def s5R : Fin 4 → ZMod 2 := ![0, 1, 0, 0]

@[expose] def s5h1Mat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def s5h2Mat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 1, 1, 0; 0, 0, 1, 0; 1, 0, 0, 0]

@[expose] def s5tauMat : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def s5h1 : GL (Fin 4) (ZMod 2) :=
  ⟨s5h1Mat, s5h1Mat, by decide +kernel, by decide +kernel⟩

@[expose] def s5h2 : GL (Fin 4) (ZMod 2) :=
  ⟨s5h2Mat, s5h2Mat, by decide +kernel, by decide +kernel⟩

@[expose] def s5tau : GL (Fin 4) (ZMod 2) :=
  ⟨s5tauMat, s5tauMat, by decide +kernel, by decide +kernel⟩

private def s5m0 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0]

private def s5m1 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 0; 1, 0, 1, 1]

private def s5m2 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 1, 1, 0; 0, 0, 1, 0; 1, 0, 0, 0]

private def s5m3 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 1, 1, 1; 0, 0, 1, 0; 1, 0, 1, 1]

private def s5m4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def s5m5 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def s5m6 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]

private def s5m7 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 1, 1; 0, 1, 1, 1; 0, 0, 1, 0; 0, 0, 0, 1]

private def s5m8 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 1, 0, 1, 1]

private def s5m9 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 1, 1, 1, 0; 0, 0, 1, 0; 1, 0, 1, 1]

private def s5m10 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 1, 1; 1, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0]

private def s5m11 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 1, 1; 1, 1, 1, 0; 0, 0, 1, 0; 1, 0, 0, 0]

private def s5G : Fin 12 → GL (Fin 4) (ZMod 2) :=
  ![⟨s5m0, s5m0, by decide +kernel, by decide +kernel⟩,
    ⟨s5m1, s5m10, by decide +kernel, by decide +kernel⟩,
    ⟨s5m2, s5m2, by decide +kernel, by decide +kernel⟩,
    ⟨s5m3, s5m11, by decide +kernel, by decide +kernel⟩,
    ⟨s5m4, s5m4, by decide +kernel, by decide +kernel⟩,
    ⟨s5m5, s5m5, by decide +kernel, by decide +kernel⟩,
    ⟨s5m6, s5m6, by decide +kernel, by decide +kernel⟩,
    ⟨s5m7, s5m7, by decide +kernel, by decide +kernel⟩,
    ⟨s5m8, s5m8, by decide +kernel, by decide +kernel⟩,
    ⟨s5m9, s5m9, by decide +kernel, by decide +kernel⟩,
    ⟨s5m10, s5m1, by decide +kernel, by decide +kernel⟩,
    ⟨s5m11, s5m3, by decide +kernel, by decide +kernel⟩]

private abbrev s5isom (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  (∀ v : Fin 4 → ZMod 2, s5q (M.mulVec v) = s5q v) ∧ M.mulVec s5R = s5R

private def s5bit : List (ZMod 2) := [0, 1]

private def s5vec : List (Fin 4 → ZMod 2) :=
  s5bit.flatMap fun a => s5bit.flatMap fun b => s5bit.flatMap fun c =>
    s5bit.flatMap fun d => [![a, b, c, d]]

private def s5mk (c0 c2 c3 : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => (![c0, s5R, c2, c3] j) i

private def s5cand : List (Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  s5vec.flatMap fun c0 => s5vec.flatMap fun c2 => s5vec.map fun c3 => s5mk c0 c2 c3

private lemma s5vec_mem : ∀ v : Fin 4 → ZMod 2, v ∈ s5vec := by
  decide +kernel

private lemma s5col_one (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hR : M.mulVec s5R = s5R) :
    (fun i => M i 1) = s5R := by
  have h : M.mulVec s5R = fun i => M i 1 := by
    funext i
    simp [Matrix.mulVec, dotProduct, s5R, Fin.sum_univ_four]
  rw [h] at hR
  exact hR

private lemma s5mk_cols (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hR : M.mulVec s5R = s5R) :
    s5mk (fun i => M i 0) (fun i => M i 2) (fun i => M i 3) = M := by
  have hcol := s5col_one M hR
  funext i j
  fin_cases j
  · simp [s5mk]
  · simpa [s5mk] using (congrFun hcol i).symm
  · simp [s5mk]
  · simp [s5mk]

private lemma s5cand_mem (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hR : M.mulVec s5R = s5R) :
    M ∈ s5cand := by
  rw [s5cand, List.mem_flatMap]
  refine ⟨(fun i => M i 0), s5vec_mem _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨(fun i => M i 2), s5vec_mem _, ?_⟩
  rw [List.mem_map]
  refine ⟨(fun i => M i 3), s5vec_mem _, ?_⟩
  exact s5mk_cols M hR

private def decEqVec4Fast : DecidableEq (Fin 4 → ZMod 2) := fun u v =>
  decidable_of_iff (((List.finRange 4).all fun i => decide (u i = v i)) = true) (by
    simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies]
    exact funext_iff.symm)

private def decEqMat4Fast : DecidableEq (Matrix (Fin 4) (Fin 4) (ZMod 2)) := fun A B =>
  decidable_of_iff (((List.finRange 4).all fun i => (List.finRange 4).all fun j =>
      decide (A i j = B i j)) = true) (by
    simp only [List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies]
    exact ⟨fun h => Matrix.ext h, fun h i j => h ▸ rfl⟩)

private theorem of_decide_inst {p : Prop} {i : Decidable p} (h : @decide p i = true) : p :=
  @of_decide_eq_true p i h

private def s5mulVecF (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (v : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  fun i => M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 + M i 3 * v 3

private lemma s5mulVec_eq (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (v : Fin 4 → ZMod 2) :
    M.mulVec v = s5mulVecF M v := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, s5mulVecF]

private abbrev s5isomL (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  (∀ v ∈ s5vec, s5q (s5mulVecF M v) = s5q v) ∧ s5mulVecF M s5R = s5R

private lemma s5isomL_iff (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : s5isomL M ↔ s5isom M := by
  simp only [s5isomL, s5isom, ← s5mulVec_eq]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun v => h1 v (s5vec_mem v), h2⟩, fun ⟨h1, h2⟩ => ⟨fun v _ => h1 v, h2⟩⟩

private theorem s5_all_of_chunks {α : Type} (f : α → Bool) (n : ℕ) :
    ∀ (K : ℕ) (l : List α), l.length ≤ n * K →
      (∀ k < K, ((l.drop (n * k)).take n).all f = true) → l.all f = true
  | 0, l, hl, _ => by
      have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      rfl
  | K + 1, l, hl, h => by
      rw [← List.take_append_drop n l, List.all_append, Bool.and_eq_true]
      refine ⟨by simpa using h 0 (Nat.succ_pos K), ?_⟩
      refine s5_all_of_chunks f n K (l.drop n) (by
        rw [List.length_drop]
        rw [Nat.mul_add_one] at hl
        omega) ?_
      intro k hk
      have h' := h (k + 1) (by omega)
      rwa [show n * (k + 1) = n + n * k by rw [Nat.mul_add_one, Nat.add_comm],
        ← List.drop_drop] at h'

attribute [local instance high] decEqVec4Fast decEqMat4Fast in
private lemma s5_cand_slice_0 : ((s5vec.drop (4 * 0)).take 4).all (fun c0 =>
    (s5vec.flatMap fun c2 => s5vec.map fun c3 => s5mk c0 c2 c3).all fun N => decide (s5isomL N →
      ∃ i : Fin 12, N = (s5G i : Matrix (Fin 4) (Fin 4) (ZMod 2)))) = true := by
  decide +kernel

attribute [local instance high] decEqVec4Fast decEqMat4Fast in
private lemma s5_cand_slice_1 : ((s5vec.drop (4 * 1)).take 4).all (fun c0 =>
    (s5vec.flatMap fun c2 => s5vec.map fun c3 => s5mk c0 c2 c3).all fun N => decide (s5isomL N →
      ∃ i : Fin 12, N = (s5G i : Matrix (Fin 4) (Fin 4) (ZMod 2)))) = true := by
  decide +kernel

attribute [local instance high] decEqVec4Fast decEqMat4Fast in
private lemma s5_cand_slice_2 : ((s5vec.drop (4 * 2)).take 4).all (fun c0 =>
    (s5vec.flatMap fun c2 => s5vec.map fun c3 => s5mk c0 c2 c3).all fun N => decide (s5isomL N →
      ∃ i : Fin 12, N = (s5G i : Matrix (Fin 4) (Fin 4) (ZMod 2)))) = true := by
  decide +kernel

attribute [local instance high] decEqVec4Fast decEqMat4Fast in
private lemma s5_cand_slice_3 : ((s5vec.drop (4 * 3)).take 4).all (fun c0 =>
    (s5vec.flatMap fun c2 => s5vec.map fun c3 => s5mk c0 c2 c3).all fun N => decide (s5isomL N →
      ∃ i : Fin 12, N = (s5G i : Matrix (Fin 4) (Fin 4) (ZMod 2)))) = true := by
  decide +kernel

attribute [local instance high] decEqVec4Fast decEqMat4Fast in
private lemma s5_cand_check_fast :
    s5cand.all (fun N => decide (s5isomL N →
      ∃ i : Fin 12, N = (s5G i : Matrix (Fin 4) (Fin 4) (ZMod 2)))) = true := by
  rw [s5cand, List.all_flatMap]
  refine s5_all_of_chunks _ 4 4 _ (by decide) fun k hk => ?_
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  exacts [s5_cand_slice_0, s5_cand_slice_1, s5_cand_slice_2, s5_cand_slice_3]

private lemma s5_cand_check :
    s5cand.all (fun N => decide (s5isom N →
      ∃ i : Fin 12, N = (s5G i : Matrix (Fin 4) (Fin 4) (ZMod 2)))) = true := by
  have h := s5_cand_check_fast
  exact List.all_eq_true.mpr fun N hN => decide_eq_true fun h1 =>
    (of_decide_inst (List.all_eq_true.mp h N hN)) ((s5isomL_iff N).mpr h1)

private lemma s5_mat_enum (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hM : s5isom M) :
    ∃ i : Fin 12, M = (s5G i : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  of_decide_eq_true ((List.all_eq_true.mp s5_cand_check) M (s5cand_mem M hM.2)) hM

private lemma s5_gl_enum (g : GL (Fin 4) (ZMod 2))
    (hg : s5isom (g : Matrix (Fin 4) (Fin 4) (ZMod 2))) : ∃ i : Fin 12, g = s5G i := by
  obtain ⟨i, hi⟩ := s5_mat_enum (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) hg
  exact ⟨i, Units.ext hi⟩

private lemma s5_finite :
    ∀ i : Fin 12, s5G i ≠ 1 → s5G i ≠ s5tau →
      ((s5G i * (s5h1 * s5G i * s5h1⁻¹)⁻¹) ^ 3 = 1 ∧
          s5G i * (s5h1 * s5G i * s5h1⁻¹)⁻¹ ≠ 1) ∨
        ((s5G i * (s5h2 * s5G i * s5h2⁻¹)⁻¹) ^ 3 = 1 ∧
          s5G i * (s5h2 * s5G i * s5h2⁻¹)⁻¹ ≠ 1) := by
  decide +kernel

private lemma rckSU5_no_order_three {Y : Subgroup (GL (Fin 4) (ZMod 2))} (hY : IsPGroup 2 Y)
    {a : GL (Fin 4) (ZMod 2)} (ha : a ∈ Y) (h3 : a ^ 3 = 1) (hne : a ≠ 1) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hY.exists_orderOf_eq_pow (⟨a, ha⟩ : Y)
  have hkσ : orderOf a = 2 ^ k := by rw [← Subgroup.orderOf_mk a ha, hk]
  have hdvd3 : orderOf a ∣ 3 := (orderOf_dvd_iff_pow_eq_one).mpr h3
  rw [hkσ] at hdvd3
  have hk0 : k = 0 := by
    by_contra hne
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hne
    have h2dvd : 2 ∣ 2 ^ k := pow_dvd_pow 2 hk1
    have h2dvd3 : 2 ∣ 3 := h2dvd.trans hdvd3
    exact (by decide : ¬ (2 ∣ 3)) h2dvd3
  subst hk0
  rw [pow_zero] at hkσ
  exact hne (orderOf_eq_one_iff.mp hkσ)

theorem rckSU_s5 (Y : Subgroup (GL (Fin 4) (ZMod 2))) (hY : IsPGroup 2 Y)
    (hq : ∀ y ∈ Y, ∀ v : Fin 4 → ZMod 2,
      s5q ((y : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) = s5q v)
    (hR : ∀ y ∈ Y, (y : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec s5R = s5R)
    (h1 : s5h1 ∈ Subgroup.normalizer (Y : Set (GL (Fin 4) (ZMod 2))))
    (h2 : s5h2 ∈ Subgroup.normalizer (Y : Set (GL (Fin 4) (ZMod 2)))) :
    ∀ y ∈ Y, y = 1 ∨ y = s5tau := by
  intro y hy
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hy1, hytau⟩ := hcon
  obtain ⟨i, hi⟩ := s5_gl_enum y ⟨hq y hy, hR y hy⟩
  subst hi
  rcases s5_finite i hy1 hytau with ⟨h3, hne⟩ | ⟨h3, hne⟩
  · refine rckSU5_no_order_three hY ?_ h3 hne
    have hmem : s5h1 * s5G i * s5h1⁻¹ ∈ Y :=
      (Subgroup.mem_set_normalizer_iff.mp h1 (s5G i)).mp hy
    exact Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hmem)
  · refine rckSU5_no_order_three hY ?_ h3 hne
    have hmem : s5h2 * s5G i * s5h2⁻¹ ∈ Y :=
      (Subgroup.mem_set_normalizer_iff.mp h2 (s5G i)).mp hy
    exact Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hmem)

end CFSG.StandardType.RCKK1IIISU

module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalDiag

public section

namespace CFSG.StandardType

namespace WitOmNs

open Module QuadraticMap TableBOrth

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_map_left_of_inv {M : V →ₗ[K] V} (hMQ : ∀ u v, polar Q (M u) (M v) = polar Q u v)
    (hMM : ∀ v, M (M v) = v) (u v : V) : polar Q (M u) v = polar Q u (M v) := by
  conv_lhs => rw [← hMM v]
  exact hMQ u (M v)

theorem polar_comb_e_f {e f : Fin 2 → V} (hef : IsHypFamily Q e f) (α β : K) (j : Fin 2) :
    polar Q (α • e 0 + β • e 1) (f j) = if j = 0 then α else β := by
  rw [polar_add_left, polar_smul_left, polar_smul_left, hef.polar_ef, hef.polar_ef]
  fin_cases j <;> simp

theorem polar_e_comb_f {e f : Fin 2 → V} (hef : IsHypFamily Q e f) (γ δ : K) (i : Fin 2) :
    polar Q (e i) (γ • f 0 + δ • f 1) = if i = 0 then γ else δ := by
  rw [polar_add_right, polar_smul_right, polar_smul_right, hef.polar_ef, hef.polar_ef]
  fin_cases i <;> simp

theorem polar_comb_e_e {e f : Fin 2 → V} (hef : IsHypFamily Q e f) (α β : K) (j : Fin 2) :
    polar Q (α • e 0 + β • e 1) (e j) = 0 := by
  rw [polar_add_left, polar_smul_left, polar_smul_left, hef.polar_ee, hef.polar_ee]
  ring

theorem polar_comb_f_f {e f : Fin 2 → V} (hef : IsHypFamily Q e f) (γ δ : K) (j : Fin 2) :
    polar Q (γ • f 0 + δ • f 1) (f j) = 0 := by
  rw [polar_add_left, polar_smul_left, polar_smul_left, hef.polar_ff, hef.polar_ff]
  ring

theorem polar_sub_proj {e f : Fin 2 → V} (hef : IsHypFamily Q e f) (v : V) (i : Fin 2) :
    polar Q (v - (polar Q v (f 0) • e 0 + polar Q v (f 1) • e 1 +
      (polar Q v (e 0) • f 0 + polar Q v (e 1) • f 1))) (e i) = 0 ∧
    polar Q (v - (polar Q v (f 0) • e 0 + polar Q v (f 1) • e 1 +
      (polar Q v (e 0) • f 0 + polar Q v (e 1) • f 1))) (f i) = 0 := by
  have hfe : ∀ a b : Fin 2, polar Q (f a) (e b) = if b = a then 1 else 0 := fun a b => by
    rw [polar_comm, hef.polar_ef]
  constructor
  · rw [polar_sub_left, polar_add_left, polar_comb_e_e hef, zero_add, polar_add_left,
      polar_smul_left, polar_smul_left, hfe, hfe]
    fin_cases i <;> simp
  · rw [polar_sub_left, polar_add_left, polar_comb_e_f hef, polar_comb_f_f hef, add_zero]
    fin_cases i <;> simp

variable [CharP K 2]

theorem commute_of_hypStable {e f : Fin 2 → V} (hef : IsHypFamily Q e f) {M d : V →ₗ[K] V}
    (hMQ : ∀ u v, polar Q (M u) (M v) = polar Q u v) (hMM : ∀ v, M (M v) = v)
    (hE : ∀ i, M (e i) ∈ Submodule.span K (Set.range e))
    (hF : ∀ i, M (f i) ∈ Submodule.span K (Set.range f)) {x y z w : K}
    (hd0 : d (e 0) = x • e 0 + z • f 1) (hd1 : d (e 1) = x • e 1 + z • f 0)
    (hd2 : d (f 0) = y • e 1 + w • f 0) (hd3 : d (f 1) = y • e 0 + w • f 1)
    (hdW : ∀ u, (∀ i, polar Q u (e i) = 0) → (∀ i, polar Q u (f i) = 0) → d u = u) (v : V) :
    M (d v) = d (M v) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have key := polar_map_left_of_inv hMQ hMM
  obtain ⟨A0, hA0⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hE 0)
  obtain ⟨A1, hA1⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hE 1)
  obtain ⟨C0, hC0⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hF 0)
  obtain ⟨C1, hC1⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hF 1)
  rw [Fin.sum_univ_two] at hA0 hA1 hC0 hC1
  have r : ∀ i j : Fin 2, polar Q (M (e i)) (f j) = polar Q (e i) (M (f j)) :=
    fun i j => key (e i) (f j)
  have r00 := r 0 0
  have r01 := r 0 1
  have r10 := r 1 0
  have r11 := r 1 1
  rw [← hA0, ← hC0, polar_comb_e_f hef, polar_e_comb_f hef] at r00
  rw [← hA0, ← hC1, polar_comb_e_f hef, polar_e_comb_f hef] at r01
  rw [← hA1, ← hC0, polar_comb_e_f hef, polar_e_comb_f hef] at r10
  rw [← hA1, ← hC1, polar_comb_e_f hef, polar_e_comb_f hef] at r11
  simp at r00 r01 r10 r11
  have hM0 : polar Q (M (M (e 0))) (f 0) = polar Q (e 0) (f 0) := by rw [hMM]
  have hM1 : polar Q (M (M (e 1))) (f 1) = polar Q (e 1) (f 1) := by rw [hMM]
  rw [← hA0, map_add, map_smul, map_smul, ← hA0, ← hA1, polar_add_left, polar_smul_left,
    polar_smul_left, polar_comb_e_f hef, polar_comb_e_f hef, hef.polar_ef] at hM0
  rw [← hA1, map_add, map_smul, map_smul, ← hA0, ← hA1, polar_add_left, polar_smul_left,
    polar_smul_left, polar_comb_e_f hef, polar_comb_e_f hef, hef.polar_ef] at hM1
  simp at hM0 hM1
  have hdiag : A0 0 = A1 1 := by
    have hsq : (A0 0 - A1 1) ^ 2 = 0 := by
      linear_combination hM0 - hM1 + (A1 1 ^ 2 - A0 0 * A1 1) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq)
  have g0 : M (d (e 0)) = d (M (e 0)) := by
    rw [hd0, ← hA0, map_add, map_smul, map_smul, map_add, map_smul, map_smul, ← hA0, ← hC1, hd0,
      hd1, ← r01, ← r11, ← hdiag]
    module
  have g1 : M (d (e 1)) = d (M (e 1)) := by
    rw [hd1, ← hA1, map_add, map_smul, map_smul, map_add, map_smul, map_smul, ← hA1, ← hC0, hd0,
      hd1, ← r00, ← r10, hdiag]
    module
  have g2 : M (d (f 0)) = d (M (f 0)) := by
    rw [hd2, ← hC0, map_add, map_smul, map_smul, map_add, map_smul, map_smul, ← hA1, ← hC0, hd2,
      hd3, ← r00, ← r10, hdiag]
    module
  have g3 : M (d (f 1)) = d (M (f 1)) := by
    rw [hd3, ← hC1, map_add, map_smul, map_smul, map_add, map_smul, map_smul, ← hA0, ← hC1, hd2,
      hd3, ← r01, ← r11, ← hdiag]
    module
  set h := polar Q v (f 0) • e 0 + polar Q v (f 1) • e 1 +
    (polar Q v (e 0) • f 0 + polar Q v (e 1) • f 1) with hh
  have hu := polar_sub_proj hef v
  have hMu : ∀ i, polar Q (M (v - h)) (e i) = 0 ∧ polar Q (M (v - h)) (f i) = 0 := by
    intro i
    constructor
    · fin_cases i
      · show polar Q (M (v - h)) (e 0) = 0
        rw [key, ← hA0, polar_add_right, polar_smul_right, polar_smul_right, (hu 0).1,
          (hu 1).1]
        ring
      · show polar Q (M (v - h)) (e 1) = 0
        rw [key, ← hA1, polar_add_right, polar_smul_right, polar_smul_right, (hu 0).1,
          (hu 1).1]
        ring
    · fin_cases i
      · show polar Q (M (v - h)) (f 0) = 0
        rw [key, ← hC0, polar_add_right, polar_smul_right, polar_smul_right, (hu 0).2,
          (hu 1).2]
        ring
      · show polar Q (M (v - h)) (f 1) = 0
        rw [key, ← hC1, polar_add_right, polar_smul_right, polar_smul_right, (hu 0).2,
          (hu 1).2]
        ring
  have hdu : d (v - h) = v - h := hdW _ (fun i => (hu i).1) (fun i => (hu i).2)
  have hdMu : d (M (v - h)) = M (v - h) := hdW _ (fun i => (hMu i).1) (fun i => (hMu i).2)
  have hdh : M (d h) = d (M h) := by
    rw [hh]
    simp only [map_add, map_smul, g0, g1, g2, g3]
  calc M (d v) = M (d h) + M (d (v - h)) := by rw [← map_add, ← map_add, add_sub_cancel]
    _ = d (M h) + d (M (v - h)) := by rw [hdh, hdu, hdMu]
    _ = d (M v) := by rw [← map_add, ← map_add, add_sub_cancel]

end WitOmNs

end CFSG.StandardType

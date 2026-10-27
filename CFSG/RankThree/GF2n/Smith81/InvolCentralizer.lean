module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.GF2n.Smith81

open scoped Matrix

variable {K : Type} [Field K]

@[expose] abbrev involNilOne (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

@[expose] abbrev involNilTwo (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]

@[expose] def involOfCols (p : Fin 4 → Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => p j i

theorem mul_involOfCols (N : Matrix (Fin 4) (Fin 4) K) (p : Fin 4 → Fin 4 → K) :
    N * involOfCols p = involOfCols (fun j => N *ᵥ p j) := by
  ext i j
  simp [involOfCols, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem involOfCols_mul (A : Matrix (Fin 4) (Fin 4) K) (p : Fin 4 → Fin 4 → K) :
    involOfCols p * A = involOfCols (fun j => ∑ k, A k j • p k) := by
  ext i j
  simp [involOfCols, Matrix.mul_apply, Finset.sum_apply, mul_comm]

theorem involIndepPair {V : Type} [AddCommGroup V] [Module K V] {w v : V} (hw : w ≠ 0)
    (hv : v ∉ Submodule.span K {w}) {a b : K} (h : a • w + b • v = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply hv
    rw [Submodule.mem_span_singleton]
    refine ⟨-(b⁻¹ * a), ?_⟩
    have hinv : b⁻¹ * b = 1 := inv_mul_cancel₀ hb
    linear_combination (norm := module) (-b⁻¹) • h + hinv • v
  subst hb
  simp only [zero_smul, add_zero] at h
  exact ⟨(smul_eq_zero.mp h).resolve_right hw, rfl⟩

theorem involIndepTriple {V : Type} [AddCommGroup V] [Module K V] {w p r : V} (hw : w ≠ 0)
    (hp : p ∉ Submodule.span K {w}) (hr : r ∉ Submodule.span K {w, p}) {a b c : K}
    (h : a • w + b • p + c • r = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hc : c = 0 := by
    by_contra hc
    apply hr
    rw [Submodule.mem_span_pair]
    refine ⟨-(c⁻¹ * a), -(c⁻¹ * b), ?_⟩
    have hinv : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
    linear_combination (norm := module) (-c⁻¹) • h + hinv • r
  subst hc
  simp only [zero_smul, add_zero] at h
  obtain ⟨ha, hb⟩ := involIndepPair hw hp h
  exact ⟨ha, hb, rfl⟩

theorem involExists_mulVec_ne_zero {N : Matrix (Fin 4) (Fin 4) K} (hN : N ≠ 0) :
    ∃ x : Fin 4 → K, N *ᵥ x ≠ 0 := by
  by_contra h
  push_neg at h
  apply hN
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem involNormalForm {N : Matrix (Fin 4) (Fin 4) K} (hNN : N * N = 0) (hN : N ≠ 0) :
    ∃ P : Matrix (Fin 4) (Fin 4) K, IsUnit P ∧
      (N * P = P * involNilOne K ∨ N * P = P * involNilTwo K) := by
  classical
  have hNNv : ∀ v : Fin 4 → K, N *ᵥ (N *ᵥ v) = 0 := fun v => by
    rw [Matrix.mulVec_mulVec, hNN, Matrix.zero_mulVec]
  obtain ⟨x, hx⟩ := involExists_mulVec_ne_zero hN
  obtain ⟨w, hxw⟩ : ∃ w, N *ᵥ x = w := ⟨_, rfl⟩
  rw [hxw] at hx
  have hw : w ≠ 0 := hx
  have hw2 : N *ᵥ w = 0 := by rw [← hxw]; exact hNNv x
  have key : ∀ (p : Fin 4 → Fin 4 → K) (A : Matrix (Fin 4) (Fin 4) K),
      (∀ j, N *ᵥ p j = ∑ k, A k j • p k) → N * involOfCols p = involOfCols p * A := by
    intro p A h
    rw [mul_involOfCols, involOfCols_mul]
    congr 1
    funext j
    exact h j
  by_cases hB : ∃ y : Fin 4 → K, N *ᵥ y ∉ Submodule.span K {w}
  ·
    obtain ⟨y, hy⟩ := hB
    obtain ⟨v, hyv⟩ : ∃ v, N *ᵥ y = v := ⟨_, rfl⟩
    rw [hyv] at hy
    have hv2 : N *ᵥ v = 0 := by rw [← hyv]; exact hNNv y
    have hind : LinearIndependent K ![w, v, x, y] := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hN' := congrArg (N *ᵥ ·) hc
      have h23 : c 2 • w + c 3 • v = 0 := by
        simpa [Fin.sum_univ_four, Matrix.mulVec_add, Matrix.mulVec_smul, hw2, hv2, hxw, hyv]
          using hN'
      obtain ⟨h2, h3⟩ := involIndepPair hw hy h23
      have h01 : c 0 • w + c 1 • v = 0 := by
        simpa [Fin.sum_univ_four, h2, h3] using hc
      obtain ⟨h0, h1⟩ := involIndepPair hw hy h01
      intro i
      fin_cases i <;> simp [h0, h1, h2, h3]
    have hunit : IsUnit (involOfCols ![w, v, x, y]) :=
      Matrix.linearIndependent_cols_iff_isUnit.mp hind
    refine ⟨involOfCols ![w, v, x, y], hunit, Or.inr (key _ _ fun j => ?_)⟩
    fin_cases j <;> simp [involNilTwo, hxw, hyv, hw2, hv2, Fin.sum_univ_four]
  ·
    push_neg at hB
    have hrange : LinearMap.range (Matrix.mulVecLin N) = Submodule.span K {w} := by
      apply le_antisymm
      · rintro _ ⟨y, rfl⟩
        simpa using hB y
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact ⟨x, by simpa using hxw⟩
    have hfin : Module.finrank K (LinearMap.ker (Matrix.mulVecLin N)) = 3 := by
      have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin N)
      rw [hrange, finrank_span_singleton hw] at h
      simp only [Module.finrank_fin_fun] at h
      omega
    have hmemW : ∀ z : Fin 4 → K, z ∈ LinearMap.ker (Matrix.mulVecLin N) ↔ N *ᵥ z = 0 :=
      fun z => by simp [LinearMap.mem_ker]
    have hwW : w ∈ LinearMap.ker (Matrix.mulVecLin N) := (hmemW w).mpr hw2
    have hsub1 : Submodule.span K {w} ≤ LinearMap.ker (Matrix.mulVecLin N) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hwW
    have hlt1 : Submodule.span K {w} < LinearMap.ker (Matrix.mulVecLin N) := by
      refine lt_of_le_of_ne hsub1 ?_
      intro heq
      have h1 : Module.finrank K (Submodule.span K {w}) =
          Module.finrank K (LinearMap.ker (Matrix.mulVecLin N)) := by rw [heq]
      rw [finrank_span_singleton hw, hfin] at h1
      omega
    obtain ⟨p1, hp1W, hp1⟩ := SetLike.exists_of_lt hlt1
    have hp1N : N *ᵥ p1 = 0 := (hmemW p1).mp hp1W
    have hsub2 : Submodule.span K {w, p1} ≤ LinearMap.ker (Matrix.mulVecLin N) := by
      rw [Submodule.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hwW
      · exact hp1W
    have hfin2 : Module.finrank K (Submodule.span K {w, p1}) ≤ 2 := by
      have h := finrank_span_finset_le_card (R := K) ({w, p1} : Finset (Fin 4 → K))
      have hc : ({w, p1} : Finset (Fin 4 → K)).card ≤ 2 := Finset.card_le_two
      have hcoe : (({w, p1} : Finset (Fin 4 → K)) : Set (Fin 4 → K)) = {w, p1} := by simp
      unfold Set.finrank at h
      rw [hcoe] at h
      omega
    have hlt2 : Submodule.span K {w, p1} < LinearMap.ker (Matrix.mulVecLin N) := by
      refine lt_of_le_of_ne hsub2 ?_
      intro heq
      have h1 : Module.finrank K (Submodule.span K {w, p1}) =
          Module.finrank K (LinearMap.ker (Matrix.mulVecLin N)) := by rw [heq]
      rw [hfin] at h1
      omega
    obtain ⟨p2, hp2W, hp2⟩ := SetLike.exists_of_lt hlt2
    have hp2N : N *ᵥ p2 = 0 := (hmemW p2).mp hp2W
    have hind : LinearIndependent K ![w, p1, p2, x] := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hN' := congrArg (N *ᵥ ·) hc
      have h3 : c 3 • w = 0 := by
        simpa [Fin.sum_univ_four, Matrix.mulVec_add, Matrix.mulVec_smul, hw2, hp1N, hp2N, hxw]
          using hN'
      have hc3 : c 3 = 0 := (smul_eq_zero.mp h3).resolve_right hw
      have h012 : c 0 • w + c 1 • p1 + c 2 • p2 = 0 := by
        simpa [Fin.sum_univ_four, hc3] using hc
      obtain ⟨h0, h1, h2⟩ := involIndepTriple hw hp1 hp2 h012
      intro i
      fin_cases i <;> simp [hc3, h0, h1, h2]
    have hunit : IsUnit (involOfCols ![w, p1, p2, x]) :=
      Matrix.linearIndependent_cols_iff_isUnit.mp hind
    refine ⟨involOfCols ![w, p1, p2, x], hunit, Or.inl (key _ _ fun j => ?_)⟩
    fin_cases j <;> simp [involNilOne, hxw, hp1N, hp2N, hw2, Fin.sum_univ_four]

theorem involPatOne {g : Matrix (Fin 4) (Fin 4) K} (hg : g * involNilOne K = involNilOne K * g) :
    g 1 0 = 0 ∧ g 2 0 = 0 ∧ g 3 0 = 0 ∧ g 3 1 = 0 ∧ g 3 2 = 0 ∧ g 0 0 = g 3 3 := by
  have h13 := congrFun (congrFun hg 1) 3
  have h23 := congrFun (congrFun hg 2) 3
  have h33 := congrFun (congrFun hg 3) 3
  have h03 := congrFun (congrFun hg 0) 3
  have h01 := congrFun (congrFun hg 0) 1
  have h02 := congrFun (congrFun hg 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four, involNilOne] at h13 h23 h33 h03 h01 h02
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h13
  · linear_combination h23
  · linear_combination h33
  · linear_combination -h01
  · linear_combination -h02
  · linear_combination h03

theorem involPatTwo {g : Matrix (Fin 4) (Fin 4) K} (hg : g * involNilTwo K = involNilTwo K * g) :
    g 2 0 = 0 ∧ g 2 1 = 0 ∧ g 3 0 = 0 ∧ g 3 1 = 0 ∧ g 0 0 = g 2 2 ∧ g 0 1 = g 2 3 ∧
      g 1 0 = g 3 2 ∧ g 1 1 = g 3 3 := by
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  have h10 := congrFun (congrFun hg 1) 0
  have h11 := congrFun (congrFun hg 1) 1
  have h02 := congrFun (congrFun hg 0) 2
  have h03 := congrFun (congrFun hg 0) 3
  have h12 := congrFun (congrFun hg 1) 2
  have h13 := congrFun (congrFun hg 1) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, involNilTwo] at h00 h01 h10 h11 h02 h03 h12 h13
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination -h00
  · linear_combination -h01
  · linear_combination -h10
  · linear_combination -h11
  · linear_combination h02
  · linear_combination h03
  · linear_combination h12
  · linear_combination h13

@[expose] def involBlkOne (g : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 2) (Fin 2) K :=
  !![g 1 1, g 1 2; g 2 1, g 2 2]

@[expose] def involBlkTwo (g : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 2) (Fin 2) K :=
  !![g 0 0, g 0 1; g 1 0, g 1 1]

theorem involBlkOne_one : involBlkOne (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [involBlkOne]

theorem involBlkTwo_one : involBlkTwo (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [involBlkTwo]

theorem involCorner_mul_one {g h : Matrix (Fin 4) (Fin 4) K}
    (hg : g * involNilOne K = involNilOne K * g) (hh : h * involNilOne K = involNilOne K * h) :
    (g * h) 0 0 = g 0 0 * h 0 0 := by
  obtain ⟨g10, g20, g30, -⟩ := involPatOne hg
  obtain ⟨h10, h20, h30, -⟩ := involPatOne hh
  simp [Matrix.mul_apply, Fin.sum_univ_four, h10, h20, h30]

theorem involBlkOne_mul {g h : Matrix (Fin 4) (Fin 4) K}
    (hg : g * involNilOne K = involNilOne K * g) (hh : h * involNilOne K = involNilOne K * h) :
    involBlkOne (g * h) = involBlkOne g * involBlkOne h := by
  obtain ⟨g10, g20, -, -, -⟩ := involPatOne hg
  obtain ⟨-, -, -, h31, h32, -⟩ := involPatOne hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [involBlkOne, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, g10, g20, h31, h32]

theorem involBlkTwo_mul {g h : Matrix (Fin 4) (Fin 4) K}
    (hg : g * involNilTwo K = involNilTwo K * g) (hh : h * involNilTwo K = involNilTwo K * h) :
    involBlkTwo (g * h) = involBlkTwo g * involBlkTwo h := by
  obtain ⟨g20, g21, g30, g31, -⟩ := involPatTwo hg
  obtain ⟨h20, h21, h30, h31, -⟩ := involPatTwo hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [involBlkTwo, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, g20, g21, g30,
      g31, h20, h21, h30, h31]

theorem involPow_four_eq_one {R : Type} [Ring R] {G : R} (h2 : (2 : R) = 0)
    (h : (G - 1) ^ 4 = 0) : G ^ 4 = 1 := by
  obtain ⟨E, rfl⟩ : ∃ E, G = 1 + E := ⟨G - 1, by abel⟩
  have h' : E ^ 4 = 0 := by simpa using h
  have h4 : (4 : R) = 0 := by rw [show (4 : R) = 2 * 2 by norm_num, h2, zero_mul]
  have h6 : (6 : R) = 0 := by rw [show (6 : R) = 2 * 3 by norm_num, h2, zero_mul]
  have e : (1 + E) ^ 4 = 1 + 4 * E + 6 * E ^ 2 + 4 * E ^ 3 + E ^ 4 := by noncomm_ring
  rw [e, h4, h6]
  simp [h']

theorem involMatrix_two_eq_zero [CharP K 2] : (2 : Matrix (Fin 4) (Fin 4) K) = 0 := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [← map_ofNat (algebraMap K (Matrix (Fin 4) (Fin 4) K)) 2, h2K, map_zero]

theorem involSq_zero_of_shape {E : Matrix (Fin 4) (Fin 4) K} (h0 : ∀ i, E i 0 = 0)
    (h1 : ∀ i, E i 1 = 0) (h2 : ∀ j, E 2 j = 0) (h3 : ∀ j, E 3 j = 0) : E * E = 0 := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_four, h0, h1, h2, h3]

theorem involCube_zero_of_shape {E : Matrix (Fin 4) (Fin 4) K} (h00 : E 0 0 = 0)
    (h10 : E 1 0 = 0) (h11 : E 1 1 = 0) (h12 : E 1 2 = 0) (h20 : E 2 0 = 0) (h21 : E 2 1 = 0)
    (h22 : E 2 2 = 0) (h30 : E 3 0 = 0) (h31 : E 3 1 = 0) (h32 : E 3 2 = 0) (h33 : E 3 3 = 0) :
    E ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_four, h00, h10, h11, h12, h20, h21, h22,
      h30, h31, h32, h33]

section Homs

variable (Y : Subgroup (GL (Fin 4) K))

@[expose] noncomputable def involCornerOne
    (hY : ∀ g ∈ Y, (g : Matrix (Fin 4) (Fin 4) K) * involNilOne K = involNilOne K * g)
    (g : GL (Fin 4) K) (hg : g ∈ Y) : Kˣ :=
  Units.mk ((g : Matrix (Fin 4) (Fin 4) K) 0 0)
    (((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 0)
    (by
      have h := involCorner_mul_one (hY g hg) (hY _ (Y.inv_mem hg))
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq] at h
      exact h.symm)
    (by
      have h := involCorner_mul_one (hY _ (Y.inv_mem hg)) (hY g hg)
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq] at h
      exact h.symm)

@[expose] noncomputable def involBlockOne
    (hY : ∀ g ∈ Y, (g : Matrix (Fin 4) (Fin 4) K) * involNilOne K = involNilOne K * g)
    (g : GL (Fin 4) K) (hg : g ∈ Y) : GL (Fin 2) K :=
  Units.mk (involBlkOne (g : Matrix (Fin 4) (Fin 4) K))
    (involBlkOne ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (by
      rw [← involBlkOne_mul (hY g hg) (hY _ (Y.inv_mem hg)), ← Units.val_mul, mul_inv_cancel,
        Units.val_one, involBlkOne_one])
    (by
      rw [← involBlkOne_mul (hY _ (Y.inv_mem hg)) (hY g hg), ← Units.val_mul, inv_mul_cancel,
        Units.val_one, involBlkOne_one])

@[expose] noncomputable def involHomOne
    (hY : ∀ g ∈ Y, (g : Matrix (Fin 4) (Fin 4) K) * involNilOne K = involNilOne K * g) :
    Y →* Kˣ × GL (Fin 2) K :=
  MonoidHom.mk' (fun g : Y => (involCornerOne Y hY g.1 g.2, involBlockOne Y hY g.1 g.2))
    (by
      intro a b
      refine Prod.ext (Units.ext ?_) (Units.ext ?_)
      · simp only [involCornerOne, Prod.fst_mul, Units.val_mul, Units.val_mk, Subgroup.coe_mul]
        exact involCorner_mul_one (hY a.1 a.2) (hY b.1 b.2)
      · simp only [involBlockOne, Prod.snd_mul, Units.val_mul, Units.val_mk, Subgroup.coe_mul]
        exact involBlkOne_mul (hY a.1 a.2) (hY b.1 b.2))

@[expose] noncomputable def involBlockTwo
    (hY : ∀ g ∈ Y, (g : Matrix (Fin 4) (Fin 4) K) * involNilTwo K = involNilTwo K * g)
    (g : GL (Fin 4) K) (hg : g ∈ Y) : GL (Fin 2) K :=
  Units.mk (involBlkTwo (g : Matrix (Fin 4) (Fin 4) K))
    (involBlkTwo ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (by
      rw [← involBlkTwo_mul (hY g hg) (hY _ (Y.inv_mem hg)), ← Units.val_mul, mul_inv_cancel,
        Units.val_one, involBlkTwo_one])
    (by
      rw [← involBlkTwo_mul (hY _ (Y.inv_mem hg)) (hY g hg), ← Units.val_mul, inv_mul_cancel,
        Units.val_one, involBlkTwo_one])

@[expose] noncomputable def involHomTwo
    (hY : ∀ g ∈ Y, (g : Matrix (Fin 4) (Fin 4) K) * involNilTwo K = involNilTwo K * g) :
    Y →* GL (Fin 2) K :=
  MonoidHom.mk' (fun g : Y => involBlockTwo Y hY g.1 g.2)
    (by
      intro a b
      apply Units.ext
      simp only [involBlockTwo, Units.val_mul, Units.val_mk, Subgroup.coe_mul]
      exact involBlkTwo_mul (hY a.1 a.2) (hY b.1 b.2))

theorem involHomOne_eq_one_iff
    (hY : ∀ g ∈ Y, (g : Matrix (Fin 4) (Fin 4) K) * involNilOne K = involNilOne K * g)
    (x : Y) :
    involHomOne Y hY x = 1 ↔
      (x.1 : Matrix (Fin 4) (Fin 4) K) 0 0 = 1 ∧
        involBlkOne (x.1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [involHomOne, MonoidHom.mk'_apply, Prod.fst_one, Prod.snd_one] at h1 h2
    refine ⟨?_, ?_⟩
    · have := congrArg Units.val h1
      simpa [involCornerOne] using this
    · have := congrArg Units.val h2
      simpa [involBlockOne] using this
  · rintro ⟨h1, h2⟩
    apply Prod.ext
    · apply Units.ext
      simpa [involHomOne, involCornerOne] using h1
    · apply Units.ext
      simpa [involHomOne, involBlockOne] using h2

theorem involHomTwo_eq_one_iff
    (hY : ∀ g ∈ Y, (g : Matrix (Fin 4) (Fin 4) K) * involNilTwo K = involNilTwo K * g)
    (x : Y) :
    involHomTwo Y hY x = 1 ↔ involBlkTwo (x.1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [involHomTwo, involBlockTwo] using this
  · intro h
    apply Units.ext
    simpa [involHomTwo, involBlockTwo] using h

end Homs

theorem involOne_pow_four [CharP K 2] (Y : Subgroup (GL (Fin 4) K))
    (hY : ∀ g ∈ Y, (g : Matrix (Fin 4) (Fin 4) K) * involNilOne K = involNilOne K * g)
    {x : GL (Fin 4) K} (hx : x ∈ Y) (h : involHomOne Y hY ⟨x, hx⟩ = 1) : x ^ 4 = 1 := by
  obtain ⟨h00, hB⟩ := (involHomOne_eq_one_iff Y hY ⟨x, hx⟩).mp h
  have hx00 : (x : Matrix (Fin 4) (Fin 4) K) 0 0 = 1 := h00
  have hB11 := congrFun (congrFun hB 0) 0
  have hB12 := congrFun (congrFun hB 0) 1
  have hB21 := congrFun (congrFun hB 1) 0
  have hB22 := congrFun (congrFun hB 1) 1
  simp [involBlkOne] at hB11 hB12 hB21 hB22
  obtain ⟨p10, p20, p30, p31, p32, p00⟩ := involPatOne (hY x hx)
  have hx11 : (x : Matrix (Fin 4) (Fin 4) K) 1 1 = 1 := hB11
  have hx22 : (x : Matrix (Fin 4) (Fin 4) K) 2 2 = 1 := hB22
  have hx33 : (x : Matrix (Fin 4) (Fin 4) K) 3 3 = 1 := by rw [← p00, hx00]
  have hE : ((x : Matrix (Fin 4) (Fin 4) K) - 1) ^ 3 = 0 := by
    apply involCube_zero_of_shape <;> simp only [Matrix.sub_apply, Matrix.one_apply] <;>
      simp [hx00, hx11, hx22, hx33, p10, p20, p30, p31, p32, hB12, hB21]
  have h4 : ((x : Matrix (Fin 4) (Fin 4) K) - 1) ^ 4 = 0 :=
    (pow_succ _ 3).trans (by rw [hE, zero_mul])
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact involPow_four_eq_one (involMatrix_two_eq_zero (K := K)) h4

theorem involTwo_pow_four [CharP K 2] (Y : Subgroup (GL (Fin 4) K))
    (hY : ∀ g ∈ Y, (g : Matrix (Fin 4) (Fin 4) K) * involNilTwo K = involNilTwo K * g)
    {x : GL (Fin 4) K} (hx : x ∈ Y) (h : involHomTwo Y hY ⟨x, hx⟩ = 1) : x ^ 4 = 1 := by
  have hB := (involHomTwo_eq_one_iff Y hY ⟨x, hx⟩).mp h
  have hB00 := congrFun (congrFun hB 0) 0
  have hB01 := congrFun (congrFun hB 0) 1
  have hB10 := congrFun (congrFun hB 1) 0
  have hB11 := congrFun (congrFun hB 1) 1
  simp [involBlkTwo] at hB00 hB01 hB10 hB11
  obtain ⟨p20, p21, p30, p31, p00, p01, p10, p11⟩ := involPatTwo (hY x hx)
  have hx00 : (x : Matrix (Fin 4) (Fin 4) K) 0 0 = 1 := hB00
  have hx11 : (x : Matrix (Fin 4) (Fin 4) K) 1 1 = 1 := hB11
  have hx22 : (x : Matrix (Fin 4) (Fin 4) K) 2 2 = 1 := by rw [← p00, hx00]
  have hx33 : (x : Matrix (Fin 4) (Fin 4) K) 3 3 = 1 := by rw [← p11, hx11]
  have hx23 : (x : Matrix (Fin 4) (Fin 4) K) 2 3 = 0 := by rw [← p01, hB01]
  have hx32 : (x : Matrix (Fin 4) (Fin 4) K) 3 2 = 0 := by rw [← p10, hB10]
  have hE : ((x : Matrix (Fin 4) (Fin 4) K) - 1) * ((x : Matrix (Fin 4) (Fin 4) K) - 1) = 0 := by
    apply involSq_zero_of_shape
    · intro i
      fin_cases i <;> simp [Matrix.sub_apply, Matrix.one_apply, hx00, hB10, p20, p30, hx11]
    · intro i
      fin_cases i <;> simp [Matrix.sub_apply, Matrix.one_apply, hB01, hx11, p21, p31]
    · intro j
      fin_cases j <;> simp [Matrix.sub_apply, Matrix.one_apply, p20, p21, hx22, hx23]
    · intro j
      fin_cases j <;> simp [Matrix.sub_apply, Matrix.one_apply, p30, p31, hx32, hx33]
  have h4 : ((x : Matrix (Fin 4) (Fin 4) K) - 1) ^ 4 = 0 := by
    have e : ((x : Matrix (Fin 4) (Fin 4) K) - 1) ^ 4 =
        ((x : Matrix (Fin 4) (Fin 4) K) - 1) ^ 2 * ((x : Matrix (Fin 4) (Fin 4) K) - 1) ^ 2 := by
      rw [← pow_add]
    rw [e, pow_two, hE, zero_mul]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact involPow_four_eq_one (involMatrix_two_eq_zero (K := K)) h4

theorem involKernelSplit {H : Type} [Group H] (Y : Subgroup (GL (Fin 4) K)) (ψ : Y →* H) :
    ∃ Y₀ : Subgroup (GL (Fin 4) K), Y₀ ≤ Y ∧ (∀ g ∈ Y, ∀ h ∈ Y₀, g * h * g⁻¹ ∈ Y₀) ∧
      (∀ g ∈ Y₀, ∃ hg : g ∈ Y, ψ ⟨g, hg⟩ = 1) ∧
      Nat.card Y = Nat.card Y₀ * Nat.card ψ.range := by
  refine ⟨ψ.ker.map Y.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro g hg h hh
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hh
    have hc := (MonoidHom.normal_ker ψ).conj_mem x hx ⟨g, hg⟩
    exact Subgroup.mem_map.mpr ⟨_, hc, rfl⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨x.2, MonoidHom.mem_ker.mp hx⟩
  · have hinj : Function.Injective Y.subtype := fun a b h => Subtype.ext h
    rw [Subgroup.card_map_of_injective hinj,
      Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, mul_comm]

theorem involCard_GL_two [Finite K] :
    Nat.card (GL (Fin 2) K) = (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
  letI := Fintype.ofFinite K
  rw [Matrix.card_GL_field 2, Fin.prod_univ_two, Nat.card_eq_fintype_card]
  simp

theorem involCard_units_prod [Finite K] :
    Nat.card (Kˣ × GL (Fin 2) K) =
      (Nat.card K - 1) * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K)) := by
  rw [Nat.card_prod, Nat.card_units, involCard_GL_two]

theorem involCard_even [Finite K] [CharP K 2] : Even (Nat.card K) := by
  have h2 : addOrderOf (1 : K) = 2 := CharP.eq (R := K) (CharP.addOrderOf_one K) inferInstance
  have h := addOrderOf_dvd_natCard (1 : K)
  rw [h2] at h
  exact even_iff_two_dvd.mpr h

theorem involTwo_le_card [Finite K] [CharP K 2] : 2 ≤ Nat.card K := by
  have h1 := Finite.one_lt_card (α := K)
  obtain ⟨k, hk⟩ := involCard_even (K := K)
  omega

theorem involArith {q : ℕ} (hq : Even q) (hq2 : 2 ≤ q) :
    (q - 1) * ((q ^ 2 - 1) * (q ^ 2 - q)) = q * ((q - 1) ^ 2 * (q ^ 2 - 1)) ∧
      Odd ((q - 1) ^ 2 * (q ^ 2 - 1)) ∧
    (q ^ 2 - 1) * (q ^ 2 - q) = q * ((q - 1) * (q ^ 2 - 1)) ∧
      Odd ((q - 1) * (q ^ 2 - 1)) := by
  have e : q ^ 2 - q = q * (q - 1) := by rw [Nat.mul_sub_one, sq]
  have hodd1 : Odd (q - 1) := Nat.Even.sub_odd (by omega) hq odd_one
  have hev2 : Even (q ^ 2) := Nat.even_pow.mpr ⟨hq, by norm_num⟩
  have hodd2 : Odd (q ^ 2 - 1) := Nat.Even.sub_odd (by nlinarith) hev2 odd_one
  refine ⟨?_, (hodd1.pow).mul hodd2, ?_, hodd1.mul hodd2⟩
  · rw [e]
    ring
  · rw [e]
    ring

theorem involCore_one [Finite K] [CharP K 2] (Y : Subgroup (GL (Fin 4) K))
    (hY : ∀ g ∈ Y, (g : Matrix (Fin 4) (Fin 4) K) * involNilOne K = involNilOne K * g) :
    ∃ Y₀ : Subgroup (GL (Fin 4) K), Y₀ ≤ Y ∧ (∀ g ∈ Y, ∀ h ∈ Y₀, g * h * g⁻¹ ∈ Y₀) ∧
      (∀ g ∈ Y₀, g ^ 4 = 1) ∧ ∃ d : ℕ, Nat.card Y = Nat.card Y₀ * d ∧
        ∃ m : ℕ, Odd m ∧ d ∣ Nat.card K * m := by
  obtain ⟨Y₀, hle, hnorm, hker, hcard⟩ := involKernelSplit Y (involHomOne Y hY)
  have hev := involCard_even (K := K)
  have h2 : 2 ≤ Nat.card K := involTwo_le_card (K := K)
  have hdvd : Nat.card (involHomOne Y hY).range ∣ Nat.card (Kˣ × GL (Fin 2) K) :=
    Subgroup.card_subgroup_dvd_card _
  rw [involCard_units_prod, (involArith hev h2).1] at hdvd
  refine ⟨Y₀, hle, hnorm, ?_, Nat.card (involHomOne Y hY).range, hcard,
    (Nat.card K - 1) ^ 2 * (Nat.card K ^ 2 - 1), (involArith hev h2).2.1, hdvd⟩
  intro g hg
  obtain ⟨hgY, h⟩ := hker g hg
  exact involOne_pow_four Y hY hgY h

theorem involCore_two [Finite K] [CharP K 2] (Y : Subgroup (GL (Fin 4) K))
    (hY : ∀ g ∈ Y, (g : Matrix (Fin 4) (Fin 4) K) * involNilTwo K = involNilTwo K * g) :
    ∃ Y₀ : Subgroup (GL (Fin 4) K), Y₀ ≤ Y ∧ (∀ g ∈ Y, ∀ h ∈ Y₀, g * h * g⁻¹ ∈ Y₀) ∧
      (∀ g ∈ Y₀, g ^ 4 = 1) ∧ ∃ d : ℕ, Nat.card Y = Nat.card Y₀ * d ∧
        ∃ m : ℕ, Odd m ∧ d ∣ Nat.card K * m := by
  obtain ⟨Y₀, hle, hnorm, hker, hcard⟩ := involKernelSplit Y (involHomTwo Y hY)
  have hev := involCard_even (K := K)
  have h2 : 2 ≤ Nat.card K := involTwo_le_card (K := K)
  have hdvd : Nat.card (involHomTwo Y hY).range ∣ Nat.card (GL (Fin 2) K) :=
    Subgroup.card_subgroup_dvd_card _
  rw [involCard_GL_two, (involArith hev h2).2.2.1] at hdvd
  refine ⟨Y₀, hle, hnorm, ?_, Nat.card (involHomTwo Y hY).range, hcard,
    (Nat.card K - 1) * (Nat.card K ^ 2 - 1), (involArith hev h2).2.2.2, hdvd⟩
  intro g hg
  obtain ⟨hgY, h⟩ := hker g hg
  exact involTwo_pow_four Y hY hgY h

theorem involCore [Finite K] [CharP K 2] (Y : Subgroup (GL (Fin 4) K))
    (N₀ : Matrix (Fin 4) (Fin 4) K) (hN₀ : N₀ = involNilOne K ∨ N₀ = involNilTwo K)
    (hY : ∀ g ∈ Y, (g : Matrix (Fin 4) (Fin 4) K) * N₀ = N₀ * (g : Matrix (Fin 4) (Fin 4) K)) :
    ∃ Y₀ : Subgroup (GL (Fin 4) K), Y₀ ≤ Y ∧ (∀ g ∈ Y, ∀ h ∈ Y₀, g * h * g⁻¹ ∈ Y₀) ∧
      (∀ g ∈ Y₀, g ^ 4 = 1) ∧ ∃ d : ℕ, Nat.card Y = Nat.card Y₀ * d ∧
        ∃ m : ℕ, Odd m ∧ d ∣ Nat.card K * m := by
  rcases hN₀ with rfl | rfl
  · exact involCore_one Y hY
  · exact involCore_two Y hY

theorem involution_centralizer_index [Finite K] [CharP K 2] {u : GL (Fin 4) K} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) {X : Subgroup (GL (Fin 4) K)} (hX : ∀ g ∈ X, g * u = u * g) :
    ∃ X₀ : Subgroup (GL (Fin 4) K), X₀ ≤ X ∧ (∀ g ∈ X, ∀ h ∈ X₀, g * h * g⁻¹ ∈ X₀) ∧
      (∀ g ∈ X₀, g ^ 4 = 1) ∧ ∃ d : ℕ, Nat.card X = Nat.card X₀ * d ∧
        ∃ m : ℕ, Odd m ∧ d ∣ Nat.card K * m := by
  obtain ⟨N, hNdef⟩ : ∃ N : Matrix (Fin 4) (Fin 4) K, N = (u : Matrix (Fin 4) (Fin 4) K) - 1 :=
    ⟨_, rfl⟩
  have hNN : N * N = 0 := by
    have h := congrArg Units.val hu2
    rw [Units.val_mul, Units.val_one] at h
    have h2 := involMatrix_two_eq_zero (K := K)
    rw [hNdef]
    calc ((u : Matrix (Fin 4) (Fin 4) K) - 1) * ((u : Matrix (Fin 4) (Fin 4) K) - 1)
        = (u : Matrix (Fin 4) (Fin 4) K) * u - 2 * (u : Matrix (Fin 4) (Fin 4) K) + 1 := by
          noncomm_ring
      _ = 1 - 2 * (u : Matrix (Fin 4) (Fin 4) K) + 1 := by rw [h]
      _ = (1 + 1) - 2 * (u : Matrix (Fin 4) (Fin 4) K) := by noncomm_ring
      _ = 0 := by rw [one_add_one_eq_two, h2]; simp
  have hN0 : N ≠ 0 := by
    intro h
    apply hu1
    apply Units.ext
    rw [Units.val_one]
    rw [hNdef] at h
    exact sub_eq_zero.mp h
  obtain ⟨P, hPu, hPcase⟩ := involNormalForm hNN hN0
  obtain ⟨N₀, hN₀, hPN⟩ : ∃ N₀ : Matrix (Fin 4) (Fin 4) K,
      (N₀ = involNilOne K ∨ N₀ = involNilTwo K) ∧ N * P = P * N₀ := by
    rcases hPcase with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  set Pu : GL (Fin 4) K := hPu.unit with hPu_def
  have hPuP : (Pu : Matrix (Fin 4) (Fin 4) K) = P := hPu.unit_spec
  have hPQ : P * ((Pu⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← hPuP]
    exact Units.mul_inv Pu
  have hQP : ((Pu⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P = 1 := by
    rw [← hPuP]
    exact Units.inv_mul Pu
  set Y : Subgroup (GL (Fin 4) K) := X.map (MulAut.conj Pu⁻¹).toMonoidHom with hYdef
  have hYcomm : ∀ g ∈ Y,
      (g : Matrix (Fin 4) (Fin 4) K) * N₀ = N₀ * (g : Matrix (Fin 4) (Fin 4) K) := by
    intro g' hg'
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
    have hgN : (g : Matrix (Fin 4) (Fin 4) K) * N = N * (g : Matrix (Fin 4) (Fin 4) K) := by
      have h := congrArg Units.val (hX g hg)
      rw [Units.val_mul, Units.val_mul] at h
      rw [hNdef, mul_sub, sub_mul, mul_one, one_mul, h]
    set Q : Matrix (Fin 4) (Fin 4) K := ((Pu⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      with hQdef
    have hN0' : N₀ = Q * N * P := by
      rw [mul_assoc, hPN, ← mul_assoc, hQP, one_mul]
    have hval : ((MulAut.conj Pu⁻¹).toMonoidHom g : Matrix (Fin 4) (Fin 4) K) =
        Q * (g : Matrix (Fin 4) (Fin 4) K) * P := by
      show ((Pu⁻¹ * g * (Pu⁻¹)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
      rw [inv_inv, Units.val_mul, Units.val_mul, hPuP]
    rw [hval]
    calc (Q * (g : Matrix (Fin 4) (Fin 4) K) * P) * N₀
        = Q * (g : Matrix (Fin 4) (Fin 4) K) * (P * N₀) := by simp only [mul_assoc]
      _ = Q * (g : Matrix (Fin 4) (Fin 4) K) * (N * P) := by rw [hPN]
      _ = Q * ((g : Matrix (Fin 4) (Fin 4) K) * N) * P := by simp only [mul_assoc]
      _ = Q * (N * (g : Matrix (Fin 4) (Fin 4) K)) * P := by rw [hgN]
      _ = Q * N * ((g : Matrix (Fin 4) (Fin 4) K) * P) := by simp only [mul_assoc]
      _ = Q * N * (P * (Q * (g : Matrix (Fin 4) (Fin 4) K) * P)) := by
          rw [show P * (Q * (g : Matrix (Fin 4) (Fin 4) K) * P) =
            (g : Matrix (Fin 4) (Fin 4) K) * P by
              rw [← mul_assoc, ← mul_assoc, hPQ, one_mul]]
      _ = (Q * N * P) * (Q * (g : Matrix (Fin 4) (Fin 4) K) * P) := by simp only [mul_assoc]
      _ = N₀ * (Q * (g : Matrix (Fin 4) (Fin 4) K) * P) := by rw [← hN0']
  obtain ⟨Y₀, hle, hnorm, hpow, d, hcard, m, hm, hdvd⟩ := involCore Y N₀ hN₀ hYcomm
  have hXY : Nat.card Y = Nat.card X :=
    Subgroup.card_map_of_injective (MulEquiv.injective _)
  have hXY₀ : Nat.card (Y₀.map (MulAut.conj Pu).toMonoidHom) = Nat.card Y₀ :=
    Subgroup.card_map_of_injective (MulEquiv.injective _)
  refine ⟨Y₀.map (MulAut.conj Pu).toMonoidHom, ?_, ?_, ?_, d, ?_, m, hm, hdvd⟩
  · intro h hh
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp (hle hy)
    rw [← hgy]
    have hid : (MulAut.conj Pu).toMonoidHom ((MulAut.conj Pu⁻¹).toMonoidHom g) = g := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hid]
    exact hg
  · intro g hg h hh
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    have hg' : (MulAut.conj Pu⁻¹).toMonoidHom g ∈ Y := Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    have hc := hnorm _ hg' y hy
    refine Subgroup.mem_map.mpr ⟨_, hc, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · intro h hh
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    rw [← map_pow, hpow y hy, map_one]
  · rw [hXY₀, ← hXY, hcard]

end CFSG.RankThree.GF2n.Smith81

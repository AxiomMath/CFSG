module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusNat

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis CFSG.LieType.Steinberg
open Matrix
open scoped Matrix

section Helpers

variable {F : Type} [Field F] [Finite F] [CharP F 2] {k : Type} [Field k] [CharP k 2]

theorem c2slomqns_neg_eq {ι : Type*} (v : ι → F) : -v = v := by
  ext a
  exact CharTwo.neg_eq (v a)

theorem c2slomqns_phi_single {n : ℕ} (φ : F →+* k) (b : Fin n ⊕ Fin n) :
    (fun a => φ ((Pi.single b (1 : F) : Fin n ⊕ Fin n → F) a)) = Pi.single b (1 : k) := by
  ext a
  by_cases h : a = b <;> simp [Pi.single_apply, h]

noncomputable def c2slomqns_mat {n : ℕ} (φ : F →+* k) (g : spinGroup (quadPlus n F)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k :=
  (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map φ

theorem c2slomqns_mat_mulVec {n : ℕ} (φ : F →+* k) (g : spinGroup (quadPlus n F))
    (x : Fin n ⊕ Fin n → k) : c2slomqns_mat φ g *ᵥ x = (omPlusNatRep n φ) g x := by
  simp [c2slomqns_mat, omPlusNatRep, Matrix.toLin'_apply]

theorem c2slomqns_mapVec {n : ℕ} (φ : F →+* k)
    (g : spinGroup (quadPlus n F)) (v : Fin n ⊕ Fin n → F) :
    (omPlusNatRep n φ) g (fun a => φ (v a)) =
      fun a => φ (spinAction (quadPlus n F) g v a) := by
  rw [show (omPlusNatRep n φ) g (fun a => φ (v a)) =
      (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map φ
        *ᵥ (fun a => φ (v a)) by
    simp [omPlusNatRep, Matrix.toLin'_apply]]
  ext i
  rw [show spinAction (quadPlus n F) g v =
      (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v from
    (spinMatrix_mulVec (quadPlus n F) g v).symm]
  exact (RingHom.map_mulVec φ
    (spinMatrix (quadPlus n F) g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v i).symm

theorem c2slomqns_spinAction_longRoot_plusVec {n : ℕ} (hn : 3 ≤ n)
    {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : F) (m : Fin n) (r : Bool) :
    spinAction (quadPlus n F) ((plusFrame n F hn).longRoot hij s t (.ofAdd c))
        (plusVec n F m r) =
      plusVec n F m r
        + (if m = j ∧ r = !t then c • plusVec n F i s else 0)
        + (if m = i ∧ r = !s then c • plusVec n F j t else 0) := by
  rw [HypFrame.spinAction_longRoot, plusFrame_vec, polar_quadPlus_plusVec,
    polar_quadPlus_plusVec, sub_eq_add_neg, c2slomqns_neg_eq]
  by_cases h1 : m = j ∧ r = !t <;> by_cases h2 : m = i ∧ r = !s <;> simp [h1, h2]

theorem c2slomqns_longRoot_row_inl_F {n : ℕ} (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j)
    (t : Bool) (m : Fin n ⊕ Fin n) :
    (spinMatrix (quadPlus n F) ((plusFrame n F hn).longRoot hij true t (.ofAdd 1)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl i) m =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inl i) m
        + (if m = (if t then Sum.inr j else Sum.inl j) then 1 else 0) := by
  rw [coe_spinMatrix, LinearMap.toMatrix'_apply, one_apply]
  rcases m with m | m
  · rw [show Pi.single (Sum.inl m) (1 : F) = plusVec n F m true from rfl]
    erw [c2slomqns_spinAction_longRoot_plusVec (F := F) hn hij true t 1 m true]
    cases t <;> by_cases h1 : m = i <;> by_cases h2 : m = j <;>
      simp_all [plusVec_true, plusVec_false, Pi.single_apply, ite_apply, one_smul, eq_comm]
  · rw [show Pi.single (Sum.inr m) (1 : F) = plusVec n F m false from rfl]
    erw [c2slomqns_spinAction_longRoot_plusVec (F := F) hn hij true t 1 m false]
    cases t <;> by_cases h1 : m = i <;> by_cases h2 : m = j <;>
      simp_all [plusVec_true, plusVec_false, Pi.single_apply, ite_apply, one_smul, eq_comm]

theorem c2slomqns_longRoot_row_inl {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k)
    {i j : Fin n} (hij : i ≠ j) (t : Bool) :
    ∀ m : Fin n ⊕ Fin n,
      c2slomqns_mat φ ((plusFrame n F hn).longRoot hij true t (.ofAdd 1)) (Sum.inl i) m =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) (Sum.inl i) m
          + (if m = (if t then Sum.inr j else Sum.inl j) then 1 else 0) := by
  intro m
  rw [c2slomqns_mat, Matrix.map_apply, c2slomqns_longRoot_row_inl_F (F := F) hn hij t m]
  by_cases h1 : Sum.inl i = m <;>
    by_cases h2 : m = (if t then Sum.inr j else Sum.inl j) <;>
    simp [h1, h2, one_apply, map_add, map_one, map_zero]

theorem c2slomqns_diffRoot_row_inr_F {n : ℕ} (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j)
    (m : Fin n ⊕ Fin n) :
    (spinMatrix (quadPlus n F) ((plusFrame n F hn).longRoot hij true false (.ofAdd 1)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inr j) m =
      (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Sum.inr j) m
        + (if m = Sum.inr i then 1 else 0) := by
  rw [coe_spinMatrix, LinearMap.toMatrix'_apply, one_apply]
  rcases m with m | m
  · rw [show Pi.single (Sum.inl m) (1 : F) = plusVec n F m true from rfl]
    erw [c2slomqns_spinAction_longRoot_plusVec (F := F) hn hij true false 1 m true]
    by_cases h1 : m = i <;> by_cases h2 : m = j <;>
      simp_all [plusVec_true, plusVec_false, Pi.single_apply, ite_apply, one_smul, eq_comm]
  · rw [show Pi.single (Sum.inr m) (1 : F) = plusVec n F m false from rfl]
    erw [c2slomqns_spinAction_longRoot_plusVec (F := F) hn hij true false 1 m false]
    by_cases h1 : m = i <;> by_cases h2 : m = j <;>
      simp_all [plusVec_true, plusVec_false, Pi.single_apply, ite_apply, one_smul, eq_comm]

theorem c2slomqns_diffRoot_row_inr {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k)
    {i j : Fin n} (hij : i ≠ j) :
    ∀ m : Fin n ⊕ Fin n,
      c2slomqns_mat φ ((plusFrame n F hn).longRoot hij true false (.ofAdd 1)) (Sum.inr j) m =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) (Sum.inr j) m
          + (if m = Sum.inr i then 1 else 0) := by
  intro m
  rw [c2slomqns_mat, Matrix.map_apply, c2slomqns_diffRoot_row_inr_F (F := F) hn hij m]
  by_cases h1 : Sum.inr j = m <;> by_cases h2 : m = Sum.inr i <;>
    simp [h1, h2, one_apply, map_add, map_one, map_zero]

theorem c2slomqns_coord_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : Type} [Field k] (A : Matrix ι ι k) {x : ι → k} (hx : A *ᵥ x = x) (r : ι) {b : ι}
    (hrow : ∀ m, A r m = (1 : Matrix ι ι k) r m + if m = b then 1 else 0) : x b = 0 := by
  have h := congrFun hx r
  simp only [mulVec, dotProduct, hrow, add_mul, Finset.sum_add_distrib, one_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact add_eq_left.mp h

theorem c2slomqns_fixU_mem {n : ℕ} (hn : 3 ≤ n) (φ : F →+* k)
    (x : Fin n ⊕ Fin n → k)
    (hx : x ∈ (omPlusCurtisDatum n F hn).fixU (omPlusNatRep n φ)) :
    ∃ c : k, x = c • (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) := by
  classical
  have hfix_root : ∀ s : Fin n, c2slomqns_mat φ (rootD F hn s (.ofAdd 1)) *ᵥ x = x := by
    intro s
    have hgX : rootD F hn s (.ofAdd 1) ∈ (omPlusCurtisDatum n F hn).X s := by
      rw [omPlusCurtisDatum_X, plusRootGroup_single]
      exact ⟨.ofAdd 1, rfl⟩
    have h := (CurtisDatum.mem_fixU (omPlusCurtisDatum n F hn) (omPlusNatRep n φ)).mp hx
      _ ((omPlusCurtisDatum n F hn).X_le s hgX)
    rwa [← c2slomqns_mat_mulVec] at h
  have hrootD_eq : ∀ s : Fin n,
      rootD F hn s (.ofAdd 1) =
        (plusFrame n F hn).longRoot (rootIdxD_ne n (by omega) s) true (rootSignD n s)
          (.ofAdd 1) :=
    fun _ => rfl
  have hrow_inl : ∀ s : Fin n, ∀ m : Fin n ⊕ Fin n,
      c2slomqns_mat φ (rootD F hn s (.ofAdd 1)) (Sum.inl (rootIdxD n s)) m =
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) (Sum.inl (rootIdxD n s)) m
          + (if m = (if rootSignD n s then Sum.inr (rootIdxD' n s)
              else Sum.inl (rootIdxD' n s)) then 1 else 0) := by
    intro s m
    rw [hrootD_eq s]
    exact c2slomqns_longRoot_row_inl (F := F) hn φ (rootIdxD_ne n (by omega) s) (rootSignD n s) m
  have hzero_inl : ∀ s : Fin n,
      x (if rootSignD n s then Sum.inr (rootIdxD' n s) else Sum.inl (rootIdxD' n s)) = 0 :=
    fun s => c2slomqns_coord_eq_zero _ (hfix_root s) (Sum.inl (rootIdxD n s)) (hrow_inl s)
  have hcoord : ∀ b : Fin n ⊕ Fin n, b ≠ Sum.inl (⟨0, by omega⟩ : Fin n) → x b = 0 := by
    rintro (i | i) hb
    · have hi : 0 < i.val := by
        rcases Nat.eq_zero_or_pos i.val with h | h
        · exact absurd (congrArg Sum.inl (Fin.ext h)) hb
        · exact h
      let s : Fin n := ⟨i.val - 1, by omega⟩
      have hs : s.val + 1 < n := by simp [s]; omega
      have hsi : (⟨s.val + 1, hs⟩ : Fin n) = i := Fin.ext (by simp [s]; omega)
      have hz := hzero_inl s
      rw [rootSignD_of_lt n hs] at hz
      simp only [Bool.false_eq_true, reduceIte] at hz
      rw [rootIdxD'_of_lt n hs] at hz
      rwa [hsi] at hz
    · by_cases hi : i.val + 1 < n
      · have hrow : ∀ m : Fin n ⊕ Fin n,
            c2slomqns_mat φ (rootD F hn i (.ofAdd 1)) (Sum.inr (rootIdxD' n i)) m =
              (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) (Sum.inr (rootIdxD' n i)) m
                + (if m = Sum.inr (rootIdxD n i) then 1 else 0) := by
          intro m
          rw [hrootD_eq i, rootSignD_of_lt n hi]
          exact c2slomqns_diffRoot_row_inr (F := F) hn φ (rootIdxD_ne n (by omega) i) m
        have hz := c2slomqns_coord_eq_zero _ (hfix_root i) (Sum.inr (rootIdxD' n i)) hrow
        rwa [rootIdxD_of_lt n hi] at hz
      · have hsi : i = (⟨n - 1, by omega⟩ : Fin n) := by
          apply Fin.ext
          have h1 : n ≤ i.val + 1 := Nat.le_of_not_lt hi
          have h2 : i.val + 1 ≤ n := i.isLt
          have h3 : i.val + 1 = n := le_antisymm h2 h1
          show i.val = n - 1
          omega
        have hz := hzero_inl i
        rw [rootSignD_of_not_lt n hi] at hz
        simp only [reduceIte] at hz
        have hri : rootIdxD' n i = i := Fin.ext (by rw [val_rootIdxD'_of_not_lt n hi]; omega)
        rwa [hri] at hz
  refine ⟨x (Sum.inl (⟨0, by omega⟩ : Fin n)), ?_⟩
  ext b
  by_cases hb : b = Sum.inl (⟨0, by omega⟩ : Fin n)
  · rw [hb]; simp
  · rw [hcoord b hb]; simp [hb]

end Helpers

end CFSG.LocalAnalysis.WeakClosure81

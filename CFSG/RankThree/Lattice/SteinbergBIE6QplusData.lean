module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenFixedRootData
public import CFSG.RankThree.Lattice.SteinbergBITrialityA2

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 Matrix

@[expose] def e6QpSupportList : Fin 15 → List (Fin Tag.E6.rank) :=
  ![[], [0, 5], [2, 4], [0, 2, 4, 5], [3], [0, 3, 5], [2, 3, 4], [0, 2, 3, 4, 5], [1], [0, 1, 5],
    [1, 2, 4], [0, 1, 2, 4, 5], [1, 3], [0, 1, 3, 5], [1, 2, 3, 4]]

@[expose] def e6QpSupport (m : Fin 15) : Set (Fin Tag.E6.rank) := {i | i ∈ e6QpSupportList m}

@[expose] def e6QpWord : Fin 15 → List (Fin Tag.E6.rank) :=
  ![[], [0, 5], [2, 4], [0, 2, 0, 4, 5, 4], [3], [0, 3, 5], [2, 3, 2, 4, 3, 2],
    [0, 2, 0, 3, 2, 0, 4, 3, 2, 0, 5, 4, 3, 2, 0], [1], [0, 1, 5], [1, 2, 4],
    [0, 1, 2, 0, 4, 5, 4], [1, 3, 1], [0, 1, 3, 1, 5], [1, 2, 3, 1, 2, 3, 4, 3, 1, 2, 3, 4]]

@[expose] def e6W0Word : List (Fin Tag.E6.rank) :=
  [0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1,
    5, 4, 3, 2, 0]

theorem gammaStable_finset_check : ∀ F : Finset (Fin Tag.E6.rank),
    (F ≠ Finset.univ ∧ ∀ i, i ∈ F ↔ e6Rho i ∈ F) ↔
      ∃ m : Fin 15, F = (e6QpSupportList m).toFinset := by
  decide +kernel

theorem gammaStable_iff_mem_e6QpSupport (J : Set (Fin Tag.E6.rank)) :
    (J ≠ Set.univ ∧ ∀ i, i ∈ J ↔ e6Rho i ∈ J) ↔ ∃ m, J = e6QpSupport m := by
  classical
  have hJF : ∀ i, i ∈ J ↔ i ∈ J.toFinset := fun i => Set.mem_toFinset.symm
  have huniv : J ≠ Set.univ ↔ J.toFinset ≠ Finset.univ := by
    rw [Ne, Ne, ← Set.toFinset_univ, Set.toFinset_inj]
  have hsupp : ∀ m, J = e6QpSupport m ↔ J.toFinset = (e6QpSupportList m).toFinset := fun m => by
    constructor
    · rintro rfl
      ext i
      rw [Set.mem_toFinset, List.mem_toFinset]
      rfl
    · intro h
      ext i
      rw [hJF, h, List.mem_toFinset]
      rfl
  simp only [huniv, hJF, hsupp]
  exact gammaStable_finset_check J.toFinset

theorem e6Longest_eq_of_check {L ω : List (Fin Tag.E6.rank)} (hω : ∀ i ∈ ω, i ∈ L)
    (hd : ∀ i ∈ L, ∀ k, (ω.reverse.foldr (reflect Tag.E6) (Pi.single i 1)) k ≤ 0) :
    e6Longest {i | i ∈ L} = (coxeterSystem Tag.E6).wordProd ω := by
  refine (CFSG.Monster.B.Geometry.isLongest_of_forall_isLeftDescent
    ((coxeterSystem Tag.E6).wordProd_mem_parabolic hω) fun i hi => ?_).eq_longest.symm
  rw [← (coxeterSystem Tag.E6).isRightDescent_inv_iff, ← CoxeterSystem.wordProd_reverse]
  have hr := IsRoot.smul (isRoot_single Tag.E6 i) ((coxeterSystem Tag.E6).wordProd ω.reverse)
  refine (smul_single_mem_negRoots_iff _ i).1 ⟨hr, ?_⟩
  rw [IsRoot.height_neg_iff hr, wordProd_smul]
  exact hd i hi

theorem e6Longest_qp (m : Fin 15) :
    e6Longest (e6QpSupport m) = (coxeterSystem Tag.E6).wordProd (e6QpWord m) := by
  have hω : ∀ m : Fin 15, ∀ i ∈ e6QpWord m, i ∈ e6QpSupportList m := by decide
  have hd : ∀ m : Fin 15, ∀ i ∈ e6QpSupportList m, ∀ k,
      ((e6QpWord m).reverse.foldr (reflect Tag.E6) (Pi.single i 1)) k ≤ 0 := by
    decide +kernel
  exact e6Longest_eq_of_check (hω m) (hd m)

theorem e6W0_eq_wordProd : e6W0 = (coxeterSystem Tag.E6).wordProd e6W0Word := by
  have h : e6Longest {i | i ∈ ([0, 1, 2, 3, 4, 5] : List (Fin Tag.E6.rank))} =
      (coxeterSystem Tag.E6).wordProd e6W0Word :=
    e6Longest_eq_of_check (by decide) (by decide +kernel)
  have hu : {i | i ∈ ([0, 1, 2, 3, 4, 5] : List (Fin Tag.E6.rank))} = Set.univ :=
    Set.eq_univ_of_forall fun i => by
      have : ∀ i : Fin Tag.E6.rank, i ∈ ([0, 1, 2, 3, 4, 5] : List (Fin Tag.E6.rank)) := by
        decide
      exact this i
  rw [← h, e6W0, hu]

@[expose] def e6RhoList : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 1], [0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 0], [1, 0, 0, 0, 0, 0]]

theorem toMat_e6RhoList : toMat Tag.E6.rank e6RhoList = rhoMatrix := by
  decide +kernel

@[expose] def e6QpDeltaList (m : Fin 15) : List (List ℤ) :=
  lsmul Tag.E6.rank (-1) (lmul Tag.E6.rank
    (lword Tag.E6.rank (cartanList Tag.E6) ((e6QpWord m).map Fin.val)) e6RhoList)

theorem toMat_e6QpDeltaList (m : Fin 15) :
    toMat Tag.E6.rank (e6QpDeltaList m) = -(wordMat Tag.E6 (e6QpWord m) * rhoMatrix) := by
  rw [e6QpDeltaList, toMat_lsmul, toMat_lmul, toMat_lword Tag.E6 (toMat_cartanList Tag.E6),
    toMat_e6RhoList, neg_one_smul]

theorem e6Delta_qp (m : Fin 15) (x : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) x = toMat Tag.E6.rank (e6QpDeltaList m) *ᵥ x := by
  rw [toMat_e6QpDeltaList, e6Delta, e6Longest_qp, wordProd_smul, ← wordMat_mulVec_eq_foldr,
    permLattice_eq_mulVec, Matrix.neg_mulVec, Matrix.mulVec_mulVec]

theorem e6W0_smul (v : Fin Tag.E6.rank → ℤ) : e6W0 • v = -permLattice e6Rho v := by
  have h : wordMat Tag.E6 e6W0Word = -rhoMatrix := by
    rw [wordMat_eq_toMat Tag.E6 e6W0Word rfl]
    decide +kernel
  rw [e6W0_eq_wordProd, wordProd_smul, ← wordMat_mulVec_eq_foldr, h, permLattice_eq_mulVec,
    Matrix.neg_mulVec]

@[expose] def e6QpPerm : Fin 15 → Equiv.Perm (Fin Tag.E6.rank) :=
  ![1, Equiv.swap 0 5, Equiv.swap 2 4, Equiv.swap 0 4 * Equiv.swap 2 5, 1, Equiv.swap 0 5, 1, 1,
    1, Equiv.swap 0 5, Equiv.swap 2 4, Equiv.swap 0 4 * Equiv.swap 2 5, Equiv.swap 1 3,
    Equiv.swap 0 5 * Equiv.swap 1 3, Equiv.swap 2 4]

theorem e6QpPerm_check : ∀ m : Fin 15,
    (∀ j, j ∈ e6QpSupportList m ↔ e6QpPerm m j ∈ e6QpSupportList m) ∧
      ∀ j ∈ e6QpSupportList m,
        toMat Tag.E6.rank (e6QpDeltaList m) *ᵥ Pi.single j 1 = Pi.single (e6QpPerm m j) 1 := by
  decide +kernel

theorem e6QpDelta_sq : ∀ m : Fin 15,
    toMat Tag.E6.rank (e6QpDeltaList m) * toMat Tag.E6.rank (e6QpDeltaList m) = 1 := by
  intro m
  rw [← toMat_lmul, ← toMat_lid]
  fin_cases m <;> exact congrArg _ (by decide +kernel)

theorem e6Delta_qp_involutive (m : Fin 15) (x : Fin Tag.E6.rank → ℤ) :
    e6Delta (e6QpSupport m) (e6Delta (e6QpSupport m) x) = x := by
  rw [e6Delta_qp, e6Delta_qp, Matrix.mulVec_mulVec, e6QpDelta_sq, Matrix.one_mulVec]

@[expose] def e6QpNonorthB (m : Fin 15) (l : List ℤ) : Bool :=
  !(decide (∀ i, i ∉ e6QpSupportList m → toVec Tag.E6.rank l i = 0)) ||
    decide (toMat Tag.E6.rank (e6QpDeltaList m) *ᵥ toVec Tag.E6.rank l = toVec Tag.E6.rank l) ||
    decide (iform (toVec Tag.E6.rank l)
      (toMat Tag.E6.rank (e6QpDeltaList m) *ᵥ toVec Tag.E6.rank l) = 0) ||
    (decide (m = 12 ∨ m = 13) &&
      decide (∀ i : Fin Tag.E6.rank, i ≠ 1 → i ≠ 3 → toVec Tag.E6.rank l i = 0))

theorem e6QpNonorthB_eq : ∀ m : Fin 15, ∀ l ∈ Tag.E6.artifactRoots, e6QpNonorthB m l = true := by
  decide +kernel

theorem e6QpDelta_nonorth {m : Fin 15} {l : List ℤ} (hl : l ∈ Tag.E6.artifactRoots)
    (h1 : ∀ i, i ∉ e6QpSupportList m → toVec Tag.E6.rank l i = 0)
    (h2 : toMat Tag.E6.rank (e6QpDeltaList m) *ᵥ toVec Tag.E6.rank l ≠ toVec Tag.E6.rank l)
    (h3 : iform (toVec Tag.E6.rank l)
      (toMat Tag.E6.rank (e6QpDeltaList m) *ᵥ toVec Tag.E6.rank l) ≠ 0) :
    (m = 12 ∨ m = 13) ∧ ∀ i : Fin Tag.E6.rank, i ≠ 1 → i ≠ 3 → toVec Tag.E6.rank l i = 0 := by
  have h := e6QpNonorthB_eq m l hl
  simp only [e6QpNonorthB, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact absurd h1 h
  · exact absurd h h2
  · exact absurd h h3
  · exact h

theorem e6QpDelta_exception : ∀ m : Fin 15, (m = 12 ∨ m = 13) →
    toMat Tag.E6.rank (e6QpDeltaList m) *ᵥ Pi.single 1 1 = Pi.single 3 1 ∧
      iform (Pi.single 1 1 : Fin Tag.E6.rank → ℤ) (Pi.single 3 1) = -1 := by
  decide +kernel

theorem e6QpDelta_D4 :
    toMat Tag.E6.rank (e6QpDeltaList 14) *ᵥ Pi.single 2 1 = Pi.single 4 1 ∧
      toMat Tag.E6.rank (e6QpDeltaList 14) *ᵥ Pi.single 4 1 = Pi.single 2 1 ∧
      toMat Tag.E6.rank (e6QpDeltaList 14) *ᵥ Pi.single 1 1 = Pi.single 1 1 ∧
      toMat Tag.E6.rank (e6QpDeltaList 14) *ᵥ Pi.single 3 1 = Pi.single 3 1 := by
  decide +kernel

@[expose] def e6QpC : Fin 15 → List (Fin Tag.E6.rank → ℤ) :=
  ![[], [![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0]], [![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0]],
    [![0, 0, 0, 0, 1, 1], ![1, 0, 1, 0, 0, 0]], [![0, 0, 0, 1, 0, 0]],
    [![0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]],
    [![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0]],
    [![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1]], [![0, 1, 0, 0, 0, 0]],
    [![0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0]],
    [![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0]],
    [![0, 0, 0, 0, 1, 1], ![0, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0]], [![0, 1, 0, 1, 0, 0]],
    [![0, 0, 0, 0, 0, 1], ![0, 1, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0]],
    [![0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 1, 2, 1, 0]]]

@[expose] def e6W0C : List (Fin Tag.E6.rank → ℤ) :=
  [![0, 0, 0, 1, 0, 0], ![0, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 2, 2, 3, 2, 1]]

theorem e6QpC_check : ∀ m : Fin 15, (e6QpC m).Nodup ∧
    (∀ β ∈ e6QpC m, List.ofFn β ∈ Tag.E6.artifactRoots ∧ 0 < height β ∧
      (∀ i, i ∉ e6QpSupportList m → β i = 0) ∧
      toMat Tag.E6.rank (e6QpDeltaList m) *ᵥ β ∈ e6QpC m) ∧
    (∀ β ∈ e6QpC m, ∀ β' ∈ e6QpC m, β ≠ β' → iform β β' = 0) ∧
    ∀ i : Fin Tag.E6.rank, (e6QpC m).foldr (fun β v => v - corootPair β v • β) (Pi.single i 1) =
      (e6QpWord m).foldr (reflect Tag.E6) (Pi.single i 1) := by
  decide +kernel

theorem e6W0C_check : e6W0C.Nodup ∧
    (∀ β ∈ e6W0C, List.ofFn β ∈ Tag.E6.artifactRoots ∧ permLattice e6Rho β = β) ∧
    (∀ β ∈ e6W0C, ∀ β' ∈ e6W0C, β ≠ β' → iform β β' = 0) ∧
    ∀ i : Fin Tag.E6.rank, e6W0C.foldr (fun β v => v - corootPair β v • β) (Pi.single i 1) =
      -permLattice e6Rho (Pi.single i 1) := by
  decide +kernel

theorem iform_rho_check : ∀ l ∈ Tag.E6.artifactRoots,
    permLattice e6Rho (toVec Tag.E6.rank l) ≠ toVec Tag.E6.rank l →
      iform (toVec Tag.E6.rank l) (permLattice e6Rho (toVec Tag.E6.rank l)) = 0 := by
  decide +kernel

end CFSG.RankThree.Lattice

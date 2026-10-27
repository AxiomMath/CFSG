module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompBasic
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
import Mathlib.LinearAlgebra.SpecialLinearGroup
import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompBlock
import CFSG.LinearAlgebra.RootGroupSL.ModelGenerate
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
public import CFSG.LinearAlgebra.RootGroupSL.ModelDefs
import CFSG.LinearAlgebra.RootGroupSL.DatumEquiv
import CFSG.LinearAlgebra.RootGroupSL.Normalizer

public section

open Polynomial Module Matrix
open CFSG.RankThree
open CFSG.LinearAlgebra.RootGroupSL
open CFSG.SeitzReduction.LinearPilot

namespace CFSG.StandardType

namespace CoordSL

private instance moduleFinite_adjoinRoot {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] :
    Module.Finite K (AdjoinRoot g) :=
  (rootPB g).finite

@[expose] def frameBlockCoords {n e s r : ℕ}
    (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (A : Finset (Fin s)) : Finset (Fin n) :=
  Finset.univ.filter fun x =>
    Sum.elim (fun ak : Fin e × Fin s => decide (ak.2 ∈ A)) (fun _ => false) (ε x) = true

theorem mem_frameBlockCoords_inl {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {A : Finset (Fin s)}
    {x : Fin n} {a : Fin e} {k : Fin s} (hx : ε x = Sum.inl (a, k)) :
    x ∈ frameBlockCoords ε A ↔ k ∈ A := by
  simp [frameBlockCoords, hx]

theorem not_mem_frameBlockCoords_inr {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {A : Finset (Fin s)}
    {x : Fin n} {z : Fin r} (hx : ε x = Sum.inr z) :
    x ∉ frameBlockCoords ε A := by
  simp [frameBlockCoords, hx]

private theorem exists_inl_of_mem_frameBlockCoords {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {A : Finset (Fin s)}
    {x : Fin n} (hx : x ∈ frameBlockCoords ε A) :
    ∃ (a : Fin e) (k : Fin s), ε x = Sum.inl (a, k) ∧ k ∈ A := by
  rw [frameBlockCoords, Finset.mem_filter] at hx
  obtain ⟨-, hp⟩ := hx
  rcases hε : ε x with ak | z
  · rcases ak with ⟨a, k⟩
    exact ⟨a, k, rfl, by simpa [hε] using hp⟩
  · exfalso
    simpa [hε] using hp

private noncomputable def pairCoordsInvFun {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s}
    (y : Fin e ⊕ Fin e) :
    ↥(frameBlockCoords ε ({i, j} : Finset (Fin s))) :=
  match y with
  | Sum.inl a => ⟨ε.symm (Sum.inl (a, i)), by simp [frameBlockCoords]⟩
  | Sum.inr a => ⟨ε.symm (Sum.inl (a, j)), by simp [frameBlockCoords]⟩

private theorem pairCoordsInvFun_apply_inl {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s} (a : Fin e) :
    (pairCoordsInvFun (ε := ε) (i := i) (j := j) (Sum.inl a)).1 =
      ε.symm (Sum.inl (a, i)) :=
  rfl

private theorem pairCoordsInvFun_apply_inr {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s} (a : Fin e) :
    (pairCoordsInvFun (ε := ε) (i := i) (j := j) (Sum.inr a)).1 =
      ε.symm (Sum.inl (a, j)) :=
  rfl

private theorem pairCoordsInvFun_injective {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s} (hij : i ≠ j) :
    Function.Injective (pairCoordsInvFun (ε := ε) (i := i) (j := j)) := by
  intro y y' h
  rcases y with a | a <;> rcases y' with b | b
  · have hv : ε.symm (Sum.inl (a, i)) = ε.symm (Sum.inl (b, i)) := by
      rw [← pairCoordsInvFun_apply_inl (ε := ε) (i := i) (j := j) a,
        ← pairCoordsInvFun_apply_inl (ε := ε) (i := i) (j := j) b]
      exact congrArg Subtype.val h
    have h' : (Sum.inl (a, i) : (Fin e × Fin s) ⊕ Fin r) = Sum.inl (b, i) := by
      simpa using congrArg ε hv
    simpa using h'
  · have hv : ε.symm (Sum.inl (a, i)) = ε.symm (Sum.inl (b, j)) := by
      rw [← pairCoordsInvFun_apply_inl (ε := ε) (i := i) (j := j) a,
        ← pairCoordsInvFun_apply_inr (ε := ε) (i := i) (j := j) b]
      exact congrArg Subtype.val h
    have h' : (Sum.inl (a, i) : (Fin e × Fin s) ⊕ Fin r) = Sum.inl (b, j) := by
      simpa using congrArg ε hv
    exact (hij (Prod.mk.inj (Sum.inl.inj h')).2).elim
  · have hv : ε.symm (Sum.inl (a, j)) = ε.symm (Sum.inl (b, i)) := by
      rw [← pairCoordsInvFun_apply_inr (ε := ε) (i := i) (j := j) a,
        ← pairCoordsInvFun_apply_inl (ε := ε) (i := i) (j := j) b]
      exact congrArg Subtype.val h
    have h' : (Sum.inl (a, j) : (Fin e × Fin s) ⊕ Fin r) = Sum.inl (b, i) := by
      simpa using congrArg ε hv
    exact (hij (Prod.mk.inj (Sum.inl.inj h')).2.symm).elim
  · have hv : ε.symm (Sum.inl (a, j)) = ε.symm (Sum.inl (b, j)) := by
      rw [← pairCoordsInvFun_apply_inr (ε := ε) (i := i) (j := j) a,
        ← pairCoordsInvFun_apply_inr (ε := ε) (i := i) (j := j) b]
      exact congrArg Subtype.val h
    have h' : (Sum.inl (a, j) : (Fin e × Fin s) ⊕ Fin r) = Sum.inl (b, j) := by
      simpa using congrArg ε hv
    simpa using h'

private theorem pairCoordsInvFun_surjective {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s} :
    Function.Surjective (pairCoordsInvFun (ε := ε) (i := i) (j := j)) := by
  intro x
  obtain ⟨a, k, hε, hkA⟩ := exists_inl_of_mem_frameBlockCoords x.2
  have hk : k = i ∨ k = j := by simpa using hkA
  rcases hk with rfl | rfl
  · refine ⟨Sum.inl a, ?_⟩
    apply Subtype.ext
    exact ((Equiv.eq_symm_apply ε).mpr hε).symm
  · refine ⟨Sum.inr a, ?_⟩
    apply Subtype.ext
    exact ((Equiv.eq_symm_apply ε).mpr hε).symm

private noncomputable def pairCoordsEquiv {n e s r : ℕ}
    (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j) :
    ↥(frameBlockCoords ε ({i, j} : Finset (Fin s))) ≃ Fin e ⊕ Fin e :=
  (Equiv.ofBijective (pairCoordsInvFun (ε := ε) (i := i) (j := j))
    ⟨pairCoordsInvFun_injective hij, pairCoordsInvFun_surjective⟩).symm

private theorem pairCoordsEquiv_symm_apply_inl {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s} (hij : i ≠ j) (a : Fin e) :
    (pairCoordsEquiv ε hij).symm (Sum.inl a) =
      ⟨ε.symm (Sum.inl (a, i)), by simp [frameBlockCoords]⟩ := by
  apply Subtype.ext
  rfl

private theorem pairCoordsEquiv_symm_apply_inr {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s} (hij : i ≠ j) (a : Fin e) :
    (pairCoordsEquiv ε hij).symm (Sum.inr a) =
      ⟨ε.symm (Sum.inl (a, j)), by simp [frameBlockCoords]⟩ := by
  apply Subtype.ext
  rfl

private theorem pairCoordsEquiv_apply_inl {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s} (hij : i ≠ j)
    (x : ↥(frameBlockCoords ε ({i, j} : Finset (Fin s)))) {a : Fin e}
    (hx : ε x.1 = Sum.inl (a, i)) :
    pairCoordsEquiv ε hij x = Sum.inl a := by
  have hx' : x = (pairCoordsEquiv ε hij).symm (Sum.inl a) := by
    rw [pairCoordsEquiv_symm_apply_inl]
    apply Subtype.ext
    exact (Equiv.eq_symm_apply ε).mpr hx
  exact (Equiv.eq_symm_apply (pairCoordsEquiv ε hij)).mp hx'

private theorem pairCoordsEquiv_apply_inr {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s} (hij : i ≠ j)
    (x : ↥(frameBlockCoords ε ({i, j} : Finset (Fin s)))) {a : Fin e}
    (hx : ε x.1 = Sum.inl (a, j)) :
    pairCoordsEquiv ε hij x = Sum.inr a := by
  have hx' : x = (pairCoordsEquiv ε hij).symm (Sum.inr a) := by
    rw [pairCoordsEquiv_symm_apply_inr]
    apply Subtype.ext
    exact (Equiv.eq_symm_apply ε).mpr hx
  exact (Equiv.eq_symm_apply (pairCoordsEquiv ε hij)).mp hx'

private noncomputable def pairBasis {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {n s r : ℕ} (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    {i j : Fin s} (hij : i ≠ j) :
    Basis (Fin (frameBlockCoords ε ({i, j} : Finset (Fin s))).card) K
      (AdjoinRoot g × AdjoinRoot g) :=
  ((rootPB g).basis.prod (rootPB g).basis).reindex
    ((pairCoordsEquiv ε hij).symm.trans
      (frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin)

private theorem pairBasis_apply {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {n s r : ℕ} (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    {i j : Fin s} (hij : i ≠ j)
    (x : ↥(frameBlockCoords ε ({i, j} : Finset (Fin s)))) :
    pairBasis (g := g) ε hij ((frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin x) =
      match pairCoordsEquiv ε hij x with
      | Sum.inl a => ((rootPB g).basis a, 0)
      | Sum.inr a => (0, (rootPB g).basis a) := by
  rw [pairBasis, Basis.reindex_apply]
  have hsymm : ((pairCoordsEquiv ε hij).symm.trans
      (frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin).symm
        (((frameBlockCoords ε ({i, j} : Finset (Fin s)))).equivFin x) =
      pairCoordsEquiv ε hij x := by
    simp
  rw [hsymm]
  rcases hq : pairCoordsEquiv ε hij x with a | a <;> simp [hq]

private noncomputable def pairFrame {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {n s r : ℕ} (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (i j : Fin s) :
    (AdjoinRoot g × AdjoinRoot g) →ₗ[K]
      ((Fin s → AdjoinRoot g) × (Fin r → K)) where
  toFun v := (Pi.single i v.1 + Pi.single j v.2, 0)
  map_add' x y := by
    ext k <;> simp [Pi.single_add, add_assoc, add_comm, add_left_comm]
  map_smul' c x := by
    ext k <;> simp [Pi.single_smul]

private theorem pairFrame_apply {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {n s r : ℕ} (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s}
    (v : AdjoinRoot g × AdjoinRoot g) :
    pairFrame (g := g) ε i j v = (Pi.single i v.1 + Pi.single j v.2, 0) := rfl

private theorem frameCoords_pairFrame_pairBasis {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (x : ↥(frameBlockCoords ε ({i, j} : Finset (Fin s)))) :
    frameCoords g ε (pairFrame (g := g) ε i j
        (pairBasis (g := g) ε hij
          ((frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin x))) =
      Pi.single x.1 1 := by
  obtain ⟨a, k, hε, hk⟩ := exists_inl_of_mem_frameBlockCoords x.2
  have hk' : k = i ∨ k = j := by simpa using hk
  rcases hk' with hki | hkj
  · rw [hki] at hε
    rw [pairBasis_apply, pairCoordsEquiv_apply_inl hij x hε]
    rw [show pairFrame (g := g) ε i j ((rootPB g).basis a, 0) = ((Pi.single i ((rootPB g).basis a) : Fin s → AdjoinRoot g), (0 : Fin r → K)) by simp [pairFrame]]
    rw [frameCoords_single_basis]
    congr 1
    rw [← hε]
    simp
  · rw [hkj] at hε
    rw [pairBasis_apply, pairCoordsEquiv_apply_inr hij x hε]
    rw [show pairFrame (g := g) ε i j (0, (rootPB g).basis a) = ((Pi.single j ((rootPB g).basis a) : Fin s → AdjoinRoot g), (0 : Fin r → K)) by simp [pairFrame]]
    rw [frameCoords_single_basis]
    congr 1
    rw [← hε]
    simp

private theorem blockOn_mulVec_single {K : Type} [Field K] {n : ℕ}
    (C : Finset (Fin n)) (X : Matrix (Fin C.card) (Fin C.card) K)
    {x : Fin n} (hx : x ∈ C) :
    CALinearPlane.blockOn K C X *ᵥ Pi.single x 1 =
      ∑ y : C, X (C.equivFin y) (C.equivFin ⟨x, hx⟩) • Pi.single y.1 1 := by
  funext p
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Finset.sum_apply]
  simp only [Pi.smul_apply]
  by_cases hp : p ∈ C
  · rw [CALinearPlane.blockOn_apply_mem C X hp hx]
    rw [Finset.sum_eq_single (⟨p, hp⟩ : C)]
    · simp
    · intro y _ hy
      rw [Pi.single_eq_of_ne]
      · simp
      · intro h
        exact hy (Subtype.ext h.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [CALinearPlane.blockOn_apply_not_mem C X (Or.inl hp)]
    have hpx : p ≠ x := fun h => hp (h ▸ hx)
    rw [Finset.sum_eq_zero]
    · simp [hpx]
    · intro y _
      rw [Pi.single_eq_of_ne]
      · simp
      · intro h
        exact hp (h ▸ y.2)

private theorem frameBlockCoords_pair_eq_union {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s} (hij : i ≠ j) :
    frameBlockCoords ε ({i, j} : Finset (Fin s)) =
      frameBlockCoords ε {i} ∪ frameBlockCoords ε {j} := by
  ext x
  rw [Finset.mem_union]
  rw [frameBlockCoords, frameBlockCoords, frameBlockCoords]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hx : ε x with ⟨a, k⟩ | z <;>
    simp [hx, Finset.mem_insert, Finset.mem_singleton]

private theorem frameBlockCoords_singleton_subset_left {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s} (hij : i ≠ j) :
    frameBlockCoords ε ({i} : Finset (Fin s)) ⊆
      frameBlockCoords ε ({i, j} : Finset (Fin s)) := by
  rw [frameBlockCoords_pair_eq_union hij]
  exact Finset.subset_union_left

private theorem frameBlockCoords_singleton_subset_right {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s} (hij : i ≠ j) :
    frameBlockCoords ε ({j} : Finset (Fin s)) ⊆
      frameBlockCoords ε ({i, j} : Finset (Fin s)) := by
  rw [frameBlockCoords_pair_eq_union hij]
  exact Finset.subset_union_right

private theorem pairBasis_repr_pair {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {n s r : ℕ} (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    {i j : Fin s} (hij : i ≠ j) (v w : AdjoinRoot g)
    (x : ↥(frameBlockCoords ε ({i, j} : Finset (Fin s)))) :
    (pairBasis (g := g) ε hij).repr (v, w)
        ((frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin x) =
      match pairCoordsEquiv ε hij x with
      | Sum.inl a => (rootPB g).basis.repr v a
      | Sum.inr a => (rootPB g).basis.repr w a := by
  rw [pairBasis, Basis.repr_reindex_apply]
  have hsymm : ((pairCoordsEquiv ε hij).symm.trans
      (frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin).symm
        (((frameBlockCoords ε ({i, j} : Finset (Fin s)))).equivFin x) =
      pairCoordsEquiv ε hij x := by
    simp
  rw [hsymm]
  rcases hq : pairCoordsEquiv ε hij x with a | a <;> simp [hq]

private theorem frameCoords_pairFrame_fst_zero {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s}
    (v : AdjoinRoot g) {p : Fin n}
    (hp : p ∉ frameBlockCoords ε ({i} : Finset (Fin s))) :
    frameCoords g ε (pairFrame (g := g) ε i j (v, 0)) p = 0 := by
  rw [frameCoords_apply]
  rcases hε : ε p with ⟨a, k⟩ | z
  · have hk : k ≠ i := by
      intro hki
      apply hp
      rw [mem_frameBlockCoords_inl (ε := ε) (A := ({i} : Finset (Fin s))) hε]
      simp [hki]
    simp [pairFrame, Pi.single_eq_of_ne hk]
  · simp [pairFrame]

private theorem frameCoords_pairFrame_snd_zero {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s}
    (w : AdjoinRoot g) {p : Fin n}
    (hp : p ∉ frameBlockCoords ε ({j} : Finset (Fin s))) :
    frameCoords g ε (pairFrame (g := g) ε i j (0, w)) p = 0 := by
  rw [frameCoords_apply]
  rcases hε : ε p with ⟨a, k⟩ | z
  · have hk : k ≠ j := by
      intro hkj
      apply hp
      rw [mem_frameBlockCoords_inl (ε := ε) (A := ({j} : Finset (Fin s))) hε]
      simp [hkj]
    simp [pairFrame, Pi.single_eq_of_ne hk]
  · simp [pairFrame]

private theorem pairBasis_apply_of_mem_singleton_left {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (x : ↥(frameBlockCoords ε ({i, j} : Finset (Fin s))))
    (hx : x.1 ∈ frameBlockCoords ε ({i} : Finset (Fin s))) :
    ∃ a : Fin (rootPB g).dim,
      pairCoordsEquiv ε hij x = Sum.inl a ∧
        pairBasis (g := g) ε hij
          ((frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin x) =
          ((rootPB g).basis a, 0) := by
  obtain ⟨a, k, hε, hk⟩ := exists_inl_of_mem_frameBlockCoords hx
  have hki : k = i := by simpa using hk
  have hεi : ε x.1 = Sum.inl (a, i) := by simpa [hki] using hε
  refine ⟨a, ?_, ?_⟩
  · rw [pairCoordsEquiv_apply_inl hij x hεi]
  · rw [pairBasis_apply, pairCoordsEquiv_apply_inl hij x hεi]

private theorem pairBasis_apply_of_mem_singleton_right {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (x : ↥(frameBlockCoords ε ({i, j} : Finset (Fin s))))
    (hx : x.1 ∈ frameBlockCoords ε ({j} : Finset (Fin s))) :
    ∃ a : Fin (rootPB g).dim,
      pairCoordsEquiv ε hij x = Sum.inr a ∧
        pairBasis (g := g) ε hij
          ((frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin x) =
          (0, (rootPB g).basis a) := by
  obtain ⟨a, k, hε, hk⟩ := exists_inl_of_mem_frameBlockCoords hx
  have hkj : k = j := by simpa using hk
  have hεj : ε x.1 = Sum.inl (a, j) := by simpa [hkj] using hε
  refine ⟨a, ?_, ?_⟩
  · rw [pairCoordsEquiv_apply_inr hij x hεj]
  · rw [pairBasis_apply, pairCoordsEquiv_apply_inr hij x hεj]

private noncomputable def pairSLHom {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {n s r : ℕ} (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    {i j : Fin s} (hij : i ≠ j) :
    _root_.SpecialLinearGroup K (AdjoinRoot g × AdjoinRoot g) →*
      Matrix.SpecialLinearGroup (Fin n) K :=
  (CALinearPlane.blockSLOn K (frameBlockCoords ε ({i, j} : Finset (Fin s)))).comp
    (Matrix.SpecialLinearGroup.toLin_equiv (pairBasis (g := g) ε hij)).symm.toMonoidHom

private theorem range_pairSLHom {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {n s r : ℕ} (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    {i j : Fin s} (hij : i ≠ j) :
    (pairSLHom (g := g) ε hij).range =
      CALinearPlane.coordBlockSL K (frameBlockCoords ε ({i, j} : Finset (Fin s))) := by
  rw [pairSLHom, MonoidHom.range_comp]
  have htop :
      ((Matrix.SpecialLinearGroup.toLin_equiv (pairBasis (g := g) ε hij)).symm.toMonoidHom).range =
        ⊤ := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using
      MulEquiv.range_eq_top (Matrix.SpecialLinearGroup.toLin_equiv (pairBasis (g := g) ε hij)).symm
  rw [htop, Subgroup.map_top, CALinearPlane.range_blockSLOn]

private theorem frameForm_pairSLHom_pairBasis {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (B : _root_.SpecialLinearGroup K (AdjoinRoot g × AdjoinRoot g))
    (x : ↥(frameBlockCoords ε ({i, j} : Finset (Fin s)))) :
    frameForm g ε (pairSLHom (g := g) ε hij B)
        (pairFrame (g := g) ε i j
          (pairBasis (g := g) ε hij
            ((frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin x))) =
      pairFrame (g := g) ε i j
        (B (pairBasis (g := g) ε hij
          ((frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin x))) := by
  classical
  let C := frameBlockCoords ε ({i, j} : Finset (Fin s))
  let pb : Module.Basis (Fin C.card) K (AdjoinRoot g × AdjoinRoot g) :=
    pairBasis (g := g) ε hij
  let X : Matrix.SpecialLinearGroup (Fin C.card) K :=
    (Matrix.SpecialLinearGroup.toLin_equiv pb).symm B
  have hX : X.1 =
      LinearMap.toMatrix pb pb
        (B : (AdjoinRoot g × AdjoinRoot g) →ₗ[K] (AdjoinRoot g × AdjoinRoot g)) :=
    Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq pb B
  have hframe :
      frameForm g ε (pairSLHom (g := g) ε hij B)
          (pairFrame (g := g) ε i j (pb (C.equivFin x))) =
        (frameCoords g ε).symm
          ((CALinearPlane.blockOn K C X.1) *ᵥ
            Pi.single x.1 1) := by
    rw [pairSLHom, MonoidHom.comp_apply]
    change frameForm g ε (CALinearPlane.blockSLOn K C X)
        (pairFrame (g := g) ε i j (pb (C.equivFin x))) = _
    rw [frameForm_apply, frameCoords_pairFrame_pairBasis]
    rw [CALinearPlane.coe_blockSLOn]
  rw [hframe]
  rw [blockOn_mulVec_single C X.1 x.2]
  rw [map_sum]
  simp only [map_smul, LinearEquiv.symm_apply_apply]
  simp_rw [← frameCoords_pairFrame_pairBasis (g := g) ε hij]
  simp only [map_smul, LinearEquiv.symm_apply_apply]
  have hsum : (∑ y : C, X.1 (C.equivFin y)
        (C.equivFin x) • pairFrame (g := g) ε i j (pb (C.equivFin y))) =
      pairFrame (g := g) ε i j
        (∑ y : C, X.1 (C.equivFin y)
          (C.equivFin x) • pb (C.equivFin y)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun y _ => (map_smul (pairFrame (g := g) ε i j) _ _).symm
  rw [hsum]
  congr 1
  calc
    (∑ y : C, X.1 (C.equivFin y) (C.equivFin x) • pb (C.equivFin y)) =
        ∑ i : Fin C.card, X.1 i (C.equivFin x) • pb i :=
      Equiv.sum_comp (C.equivFin) (fun i : Fin C.card => X.1 i (C.equivFin x) • pb i)
    _ = ∑ i : Fin C.card, pb.repr (B (pb (C.equivFin x))) i • pb i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hX, LinearMap.toMatrix_apply]
      rfl
    _ = B (pb (C.equivFin x)) := pb.sum_repr _

private theorem frameForm_pairSLHom_pairFrame {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (B : _root_.SpecialLinearGroup K (AdjoinRoot g × AdjoinRoot g))
    (v : AdjoinRoot g × AdjoinRoot g) :
    frameForm g ε (pairSLHom (g := g) ε hij B)
        (pairFrame (g := g) ε i j v) =
      pairFrame (g := g) ε i j (B v) := by
  have h : (frameForm g ε (pairSLHom (g := g) ε hij B)).comp
        (pairFrame (g := g) ε i j) =
      (pairFrame (g := g) ε i j).comp
        (B : (AdjoinRoot g × AdjoinRoot g) →ₗ[K] (AdjoinRoot g × AdjoinRoot g)) := by
    apply Module.Basis.ext
    intro i'
    let x : ↥(frameBlockCoords ε ({i, j} : Finset (Fin s))) :=
      (frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin.symm i'
    have hx : (frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin x = i' :=
      (frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin.apply_symm_apply i'
    simpa [x, hx] using
      frameForm_pairSLHom_pairBasis (g := g) ε hij B x
  exact LinearMap.congr_fun h v

private theorem matrix_entry_frameCoords_frameForm {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (M : Matrix (Fin n) (Fin n) K) (p q : Fin n) :
    M p q =
      frameCoords g ε
        (frameForm g ε M ((frameCoords g ε).symm (Pi.single q 1))) p := by
  have h := congrFun
    (frameCoords_frameForm g ε M ((frameCoords g ε).symm (Pi.single q 1))) p
  rw [LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one, Matrix.col_apply] at h
  exact h.symm

private theorem matrix_entry_pairSLHom_of_mem_pair {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (B : _root_.SpecialLinearGroup K (AdjoinRoot g × AdjoinRoot g))
    (q : ↥(frameBlockCoords ε ({i, j} : Finset (Fin s)))) (p : Fin n) :
    Subtype.val (pairSLHom (g := g) ε hij B) p q.1 =
      frameCoords g ε
        (pairFrame (g := g) ε i j
          (B (pairBasis (g := g) ε hij
            ((frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin q)))) p := by
  rw [matrix_entry_frameCoords_frameForm (g := g) (ε := ε)
    (M := Subtype.val (pairSLHom (g := g) ε hij B)) (p := p) (q := q.1)]
  have hpre : (frameCoords g ε).symm (Pi.single q.1 1) =
      pairFrame (g := g) ε i j
        (pairBasis (g := g) ε hij
          ((frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin q)) :=
    (LinearEquiv.symm_apply_eq (frameCoords g ε)).mpr
      (frameCoords_pairFrame_pairBasis (g := g) ε hij q).symm
  rw [hpre, frameForm_pairSLHom_pairFrame]

private theorem pairSLHom_blockSLk_mem_left {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (A : _root_.SpecialLinearGroup K (AdjoinRoot g)) :
    pairSLHom (g := g) ε hij
        (blockSLk (VJ := AdjoinRoot g) K (AdjoinRoot g) A) ∈
      CALinearPlane.coordBlockSL K (frameBlockCoords ε ({i} : Finset (Fin s))) := by
  letI : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  classical
  let C := frameBlockCoords ε ({i, j} : Finset (Fin s))
  let Ci := frameBlockCoords ε ({i} : Finset (Fin s))
  let Cj := frameBlockCoords ε ({j} : Finset (Fin s))
  let B : _root_.SpecialLinearGroup K (AdjoinRoot g × AdjoinRoot g) :=
    blockSLk (VJ := AdjoinRoot g) K (AdjoinRoot g) A
  have hBC : pairSLHom (g := g) ε hij B ∈ CALinearPlane.coordBlockSL K C := by
    rw [← range_pairSLHom (g := g) ε hij]
    exact ⟨B, rfl⟩
  rw [CALinearPlane.mem_coordBlockSL_iff]
  intro p q hpq
  by_cases hqC : q ∈ C
  · let x : ↥C := ⟨q, hqC⟩
    have hq_union : q ∈ Ci ∪ Cj := by
      have h := hqC
      rw [show C = Ci ∪ Cj from frameBlockCoords_pair_eq_union hij] at h
      exact h
    rcases Finset.mem_union.mp hq_union with hqCi | hqCj
    · have hpCi : p ∉ Ci := by
        rcases hpq with hp | hq'
        · exact hp
        · exact absurd hqCi hq'
      obtain ⟨a, hq_eq, hq_basis⟩ :=
        pairBasis_apply_of_mem_singleton_left (g := g) ε hij x hqCi
      have hBapply : B (pairBasis (g := g) ε hij (C.equivFin x)) =
          (A ((rootPB g).basis a), 0) := by
        rw [hq_basis]
        simp [B, blockSLk_apply]
      have hentry := matrix_entry_pairSLHom_of_mem_pair (g := g) ε hij B x p
      rw [hentry, hBapply, frameCoords_pairFrame_fst_zero (g := g) ε
        (A ((rootPB g).basis a)) hpCi]
      have hpq_ne : p ≠ x.1 := by
        intro h
        exact hpCi (h ▸ hqCi)
      have hpq_ne' : p ≠ q := fun h => hpq_ne h
      simp [hpq_ne']
    · obtain ⟨a, hq_eq, hq_basis⟩ :=
        pairBasis_apply_of_mem_singleton_right (g := g) ε hij x hqCj
      have hBapply : B (pairBasis (g := g) ε hij (C.equivFin x)) =
          pairBasis (g := g) ε hij (C.equivFin x) := by
        rw [hq_basis]
        simp [B, blockSLk_apply]
      have hentry := matrix_entry_pairSLHom_of_mem_pair (g := g) ε hij B x p
      rw [hentry, hBapply, frameCoords_pairFrame_pairBasis (g := g) ε hij x]
      simp [Pi.single_apply]
      rfl
  · exact (CALinearPlane.mem_coordBlockSL_iff.mp hBC) p q (Or.inr hqC)

private theorem frameBlockCoords_singletons_disjoint {n e s r : ℕ}
    {ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {i j : Fin s} (hij : i ≠ j) :
    Disjoint (frameBlockCoords ε ({i} : Finset (Fin s)))
      (frameBlockCoords ε ({j} : Finset (Fin s))) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  obtain ⟨a, k, hε, hk⟩ := exists_inl_of_mem_frameBlockCoords hxi
  have hki : k = i := by simpa using hk
  have hεi : ε x = Sum.inl (a, i) := by simpa [hki] using hε
  obtain ⟨b, l, hε', hl⟩ := exists_inl_of_mem_frameBlockCoords hxj
  have hlj : l = j := by simpa using hl
  have hεj : ε x = Sum.inl (b, j) := by simpa [hlj] using hε'
  have hpair : (a, i) = (b, j) := Sum.inl.inj (hεi.symm.trans hεj)
  exact hij (Prod.mk.inj hpair).2

private theorem pairSLHom_blockSLk_prodComm_mem_right {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (A : _root_.SpecialLinearGroup K (AdjoinRoot g)) :
    pairSLHom (g := g) ε hij
        (SpecialLinearGroup.congr_linearEquiv
          (LinearEquiv.prodComm K (AdjoinRoot g) (AdjoinRoot g))
          (blockSLk (VJ := AdjoinRoot g) K (AdjoinRoot g) A)) ∈
      CALinearPlane.coordBlockSL K (frameBlockCoords ε ({j} : Finset (Fin s))) := by
  letI : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  classical
  let C := frameBlockCoords ε ({i, j} : Finset (Fin s))
  let Ci := frameBlockCoords ε ({i} : Finset (Fin s))
  let Cj := frameBlockCoords ε ({j} : Finset (Fin s))
  let B : _root_.SpecialLinearGroup K (AdjoinRoot g × AdjoinRoot g) :=
    SpecialLinearGroup.congr_linearEquiv
      (LinearEquiv.prodComm K (AdjoinRoot g) (AdjoinRoot g))
      (blockSLk (VJ := AdjoinRoot g) K (AdjoinRoot g) A)
  have hBC : pairSLHom (g := g) ε hij B ∈ CALinearPlane.coordBlockSL K C := by
    rw [← range_pairSLHom (g := g) ε hij]
    exact ⟨B, rfl⟩
  rw [CALinearPlane.mem_coordBlockSL_iff]
  intro p q hpq
  by_cases hqC : q ∈ C
  · let x : ↥C := ⟨q, hqC⟩
    have hq_union : q ∈ Ci ∪ Cj := by
      have h := hqC
      rw [show C = Ci ∪ Cj from frameBlockCoords_pair_eq_union hij] at h
      exact h
    rcases Finset.mem_union.mp hq_union with hqCi | hqCj
    · obtain ⟨a, hq_eq, hq_basis⟩ :=
        pairBasis_apply_of_mem_singleton_left (g := g) ε hij x hqCi
      have hBapply : B (pairBasis (g := g) ε hij (C.equivFin x)) =
          pairBasis (g := g) ε hij (C.equivFin x) := by
        rw [hq_basis]
        simp [B, SpecialLinearGroup.congr_linearEquiv_apply_apply,
          LinearEquiv.prodComm_apply, blockSLk_apply]
      have hentry := matrix_entry_pairSLHom_of_mem_pair (g := g) ε hij B x p
      rw [hentry, hBapply, frameCoords_pairFrame_pairBasis (g := g) ε hij x]
      simp [Pi.single_apply]
      rfl
    · have hpCj : p ∉ Cj := by
        rcases hpq with hp | hq'
        · exact hp
        · exact absurd hqCj hq'
      obtain ⟨a, hq_eq, hq_basis⟩ :=
        pairBasis_apply_of_mem_singleton_right (g := g) ε hij x hqCj
      have hBapply : B (pairBasis (g := g) ε hij (C.equivFin x)) =
          (0, A ((rootPB g).basis a)) := by
        rw [hq_basis]
        simp [B, SpecialLinearGroup.congr_linearEquiv_apply_apply,
          LinearEquiv.prodComm_apply, blockSLk_apply]
      have hentry := matrix_entry_pairSLHom_of_mem_pair (g := g) ε hij B x p
      rw [hentry, hBapply, frameCoords_pairFrame_snd_zero (g := g) ε
        (A ((rootPB g).basis a)) hpCj]
      have hpq_ne : p ≠ x.1 := by
        intro h
        exact hpCj (h ▸ hqCj)
      have hpq_ne' : p ≠ q := fun h => hpq_ne h
      simp [hpq_ne']
  · exact (CALinearPlane.mem_coordBlockSL_iff.mp hBC) p q (Or.inr hqC)

private theorem pairEmbed_mulVec_apply {E : Type} [Field E] {s : ℕ}
    {a b : Fin s} (hab : a ≠ b) (M : Matrix.SpecialLinearGroup (Fin 2) E)
    (u : Fin s → E) (k : Fin s) :
    ((pairEmbed hab M).1 *ᵥ u) k =
      if k = a then (M : Matrix (Fin 2) (Fin 2) E) 0 0 * u a +
          (M : Matrix (Fin 2) (Fin 2) E) 0 1 * u b
      else if k = b then (M : Matrix (Fin 2) (Fin 2) E) 1 0 * u a +
          (M : Matrix (Fin 2) (Fin 2) E) 1 1 * u b
      else u k := by
  rw [Matrix.mulVec, dotProduct]
  by_cases hk : k = a
  · rw [if_pos hk]
    rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset (Fin s))) ?_]
    · rw [Finset.sum_insert (by simp [hab]), Finset.sum_singleton]
      simp [pairEmbed_apply, hk]
    · intro x _ hx
      rw [pairEmbed_apply_of_notMem hab M (Or.inr hx)]
      have hkx : k ≠ x := by
        intro h
        exact hx (by simpa [h.symm, hk])
      simp [Matrix.one_apply, hkx]
  · by_cases hk' : k = b
    · rw [if_neg hk, if_pos hk']
      rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset (Fin s))) ?_]
      · rw [Finset.sum_insert (by simp [hab]), Finset.sum_singleton]
        simp [pairEmbed_apply, hab, hab.symm, hk']
      · intro x _ hx
        rw [pairEmbed_apply_of_notMem hab M (Or.inr hx)]
        have hkx : k ≠ x := by
          intro h
          exact hx (by simpa [h.symm, hk'])
        simp [Matrix.one_apply, hkx]
    · rw [if_neg hk, if_neg hk']
      rw [Finset.sum_eq_single k]
      · rw [pairEmbed_apply_of_notMem hab M (Or.inl (by simpa [Finset.mem_insert,
          Finset.mem_singleton] using ⟨hk, hk'⟩))]
        simp
      · intro x _ hx
        rw [pairEmbed_apply_of_notMem hab M (Or.inl (by simpa [Finset.mem_insert,
          Finset.mem_singleton] using ⟨hk, hk'⟩))]
        simp [show k ≠ x from fun h => hx h.symm]
      · intro h
        exact absurd (Finset.mem_univ k) h

private theorem matrix_toLin_finTwoProd_apply_zero {E : Type} [Field E]
    (N : Matrix (Fin 2) (Fin 2) E) :
    Matrix.toLin (Module.Basis.finTwoProd E) (Module.Basis.finTwoProd E) N (1, 0) =
      (N 0 0, N 1 0) := by
  rw [← Module.Basis.finTwoProd_zero]
  rw [Matrix.toLin_self]
  simp [Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one, Fin.sum_univ_two,
    Prod.ext_iff]

private theorem matrix_toLin_finTwoProd_apply_one {E : Type} [Field E]
    (N : Matrix (Fin 2) (Fin 2) E) :
    Matrix.toLin (Module.Basis.finTwoProd E) (Module.Basis.finTwoProd E) N (0, 1) =
      (N 0 1, N 1 1) := by
  rw [← Module.Basis.finTwoProd_one]
  rw [Matrix.toLin_self]
  simp [Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one, Fin.sum_univ_two,
    Prod.ext_iff]

private theorem pairEmbed_mulVec_eq_self_of_zero {E : Type} [Field E] {s : ℕ}
    {a b : Fin s} (hab : a ≠ b) (M : Matrix.SpecialLinearGroup (Fin 2) E)
    (u : Fin s → E) (ha : u a = 0) (hb : u b = 0) :
    (pairEmbed hab M).1 *ᵥ u = u := by
  funext k
  rw [pairEmbed_mulVec_apply]
  by_cases hk : k = a
  · rw [if_pos hk]
    simp [hk, ha, hb]
  · by_cases hk' : k = b
    · rw [if_neg hk, if_pos hk']
      simp [hk', ha, hb]
    · rw [if_neg hk, if_neg hk']

private theorem matrix_toLin_finTwoProd_basis_zero {E : Type} [Field E]
    (N : Matrix (Fin 2) (Fin 2) E) (c : E) :
    Matrix.toLin (Module.Basis.finTwoProd E) (Module.Basis.finTwoProd E) N (c, 0) =
      (c * N 0 0, c * N 1 0) := by
  have h1 : ((c, 0) : E × E) = c • ((1, 0) : E × E) := by
    ext <;> simp
  rw [h1, map_smul, matrix_toLin_finTwoProd_apply_zero]
  rfl

private theorem matrix_toLin_finTwoProd_basis_one {E : Type} [Field E]
    (N : Matrix (Fin 2) (Fin 2) E) (c : E) :
    Matrix.toLin (Module.Basis.finTwoProd E) (Module.Basis.finTwoProd E) N (0, c) =
      (c * N 0 1, c * N 1 1) := by
  have h1 : ((0, c) : E × E) = c • ((0, 1) : E × E) := by
    ext <;> simp
  rw [h1, map_smul, matrix_toLin_finTwoProd_apply_one]
  rfl

private theorem matrix_entry_theta_pairEmbed_of_mem_pair {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (N : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot g))
    (q : ↥(frameBlockCoords ε ({i, j} : Finset (Fin s)))) (p : Fin n) :
    Subtype.val (theta g ε (pairEmbed hij N)) p q.1 =
      frameCoords g ε
        (blockAct (r := r) g (pairEmbed hij N)
          (pairFrame (g := g) ε i j
            (pairBasis (g := g) ε hij
              ((frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin q)))) p := by
  rw [matrix_entry_frameCoords_frameForm (g := g) (ε := ε)
    (M := Subtype.val (theta g ε (pairEmbed hij N))) (p := p) (q := q.1)]
  have htheta : Subtype.val (theta g ε (pairEmbed hij N)) =
      thetaMat g ε (pairEmbed hij N) := rfl
  rw [htheta, frameForm_thetaMat]
  have hpre : (frameCoords g ε).symm (Pi.single q.1 1) =
      pairFrame (g := g) ε i j
        (pairBasis (g := g) ε hij
          ((frameBlockCoords ε ({i, j} : Finset (Fin s))).equivFin q)) :=
    (LinearEquiv.symm_apply_eq (frameCoords g ε)).mpr
      (frameCoords_pairFrame_pairBasis (g := g) ε hij q).symm
  rw [hpre]

private theorem blockAct_pairEmbed_pairFrame_zero {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (N : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot g))
    (a : Fin (rootPB g).dim) :
    blockAct (r := r) g (pairEmbed hij N)
        (pairFrame (g := g) ε i j ((rootPB g).basis a, 0)) =
      pairFrame (g := g) ε i j
        ((Matrix.SpecialLinearGroup.toLin_equiv (Module.Basis.finTwoProd (AdjoinRoot g)) N)
          ((rootPB g).basis a, 0)) := by
  have hA : (Matrix.SpecialLinearGroup.toLin_equiv (Module.Basis.finTwoProd (AdjoinRoot g)) N)
        ((rootPB g).basis a, 0) =
      ((rootPB g).basis a * N.1 0 0, (rootPB g).basis a * N.1 1 0) := by
    change Matrix.toLin (Module.Basis.finTwoProd (AdjoinRoot g))
      (Module.Basis.finTwoProd (AdjoinRoot g)) N.1 ((rootPB g).basis a, 0) = _
    exact matrix_toLin_finTwoProd_basis_zero N.1 ((rootPB g).basis a)
  rw [hA, blockAct_apply]
  simp only [pairFrame_apply, Pi.single_zero, add_zero]
  apply Prod.ext
  · funext k
    dsimp only [Prod.fst, Prod.snd]
    erw [pairEmbed_mulVec_apply]
    by_cases hk : k = i
    · rw [if_pos hk]
      simp [Pi.single_apply, hk, hij, Ne.symm hij, mul_comm]
    · by_cases hk' : k = j
      · rw [if_neg hk, if_pos hk']
        simp [Pi.single_apply, hk, hk', hij, Ne.symm hij, mul_comm]
      · rw [if_neg hk, if_neg hk']
        simp [Pi.single_apply, hk, hk']
  · rfl

private theorem blockAct_pairEmbed_pairFrame_one {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (N : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot g))
    (a : Fin (rootPB g).dim) :
    blockAct (r := r) g (pairEmbed hij N)
        (pairFrame (g := g) ε i j (0, (rootPB g).basis a)) =
      pairFrame (g := g) ε i j
        ((Matrix.SpecialLinearGroup.toLin_equiv (Module.Basis.finTwoProd (AdjoinRoot g)) N)
          (0, (rootPB g).basis a)) := by
  have hA : (Matrix.SpecialLinearGroup.toLin_equiv (Module.Basis.finTwoProd (AdjoinRoot g)) N)
        (0, (rootPB g).basis a) =
      ((rootPB g).basis a * N.1 0 1, (rootPB g).basis a * N.1 1 1) := by
    change Matrix.toLin (Module.Basis.finTwoProd (AdjoinRoot g))
      (Module.Basis.finTwoProd (AdjoinRoot g)) N.1 (0, (rootPB g).basis a) = _
    exact matrix_toLin_finTwoProd_basis_one N.1 ((rootPB g).basis a)
  rw [hA, blockAct_apply]
  simp only [pairFrame_apply, Pi.single_zero, zero_add]
  apply Prod.ext
  · funext k
    dsimp only [Prod.fst, Prod.snd]
    erw [pairEmbed_mulVec_apply]
    by_cases hk : k = i
    · rw [if_pos hk]
      simp [Pi.single_apply, hk, hij, Ne.symm hij, mul_comm]
    · by_cases hk' : k = j
      · rw [if_neg hk, if_pos hk']
        simp [Pi.single_apply, hk, hk', hij, Ne.symm hij, mul_comm]
      · rw [if_neg hk, if_neg hk']
        simp [Pi.single_apply, hk, hk']
  · rfl

private theorem frameCoords_symm_single_zero_pair {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    {q : Fin n} (hq : q ∉ frameBlockCoords ε ({i, j} : Finset (Fin s))) :
    ((frameCoords g ε).symm (Pi.single q 1)).1 i = 0 ∧
      ((frameCoords g ε).symm (Pi.single q 1)).1 j = 0 := by
  have hzero : ∀ k : Fin s, k ∈ ({i, j} : Finset (Fin s)) →
      ((frameCoords g ε).symm (Pi.single q 1)).1 k = 0 := by
    intro k hk
    apply (rootPB g).basis.repr.injective
    ext a
    let y : Fin n := ε.symm (Sum.inl (a, k))
    have hyC : y ∈ frameBlockCoords ε ({i, j} : Finset (Fin s)) := by
      rw [mem_frameBlockCoords_inl (ε := ε) (A := ({i, j} : Finset (Fin s)))
        (Equiv.apply_symm_apply ε (Sum.inl (a, k)))]
      exact hk
    have hyq : y ≠ q := by
      intro hqy
      exact hq (by rwa [hqy] at hyC)
    have h := congrFun
      ((frameCoords g ε).apply_symm_apply (Pi.single q 1)) y
    rw [frameCoords_apply] at h
    simp [y, Equiv.apply_symm_apply] at h
    rw [Pi.single_eq_of_ne hyq] at h
    simpa using h
  exact ⟨hzero i (by simp), hzero j (by simp)⟩

private theorem matrix_entry_theta_pairEmbed_of_not_mem_pair {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (N : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot g))
    {q : Fin n} (hq : q ∉ frameBlockCoords ε ({i, j} : Finset (Fin s))) (p : Fin n) :
    Subtype.val (theta g ε (pairEmbed hij N)) p q = if p = q then 1 else 0 := by
  rw [matrix_entry_frameCoords_frameForm (g := g) (ε := ε)
    (M := Subtype.val (theta g ε (pairEmbed hij N))) (p := p) (q := q)]
  have htheta : Subtype.val (theta g ε (pairEmbed hij N)) =
      thetaMat g ε (pairEmbed hij N) := rfl
  rw [htheta, frameForm_thetaMat]
  let v := (frameCoords g ε).symm (Pi.single q 1)
  have hzero := frameCoords_symm_single_zero_pair (g := g) ε hij hq
  have hfix : blockAct (r := r) g (pairEmbed hij N) v = v := by
    rw [blockAct_apply]
    have hW : (pairEmbed hij N).1 *ᵥ v.1 = v.1 :=
      pairEmbed_mulVec_eq_self_of_zero hij N v.1 hzero.1 hzero.2
    rw [hW]
  rw [hfix, LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply]

private theorem pairSLHom_restrictSL_eq_theta_pairEmbed {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (A : _root_.SpecialLinearGroup (AdjoinRoot g) (AdjoinRoot g × AdjoinRoot g)) :
    pairSLHom (g := g) ε hij
        (CFSG.LinearAlgebra.RootGroupSL.restrictSL (E := AdjoinRoot g)
          (VJ := AdjoinRoot g × AdjoinRoot g) K A) =
      theta g ε (pairEmbed hij
        ((Matrix.SpecialLinearGroup.toLin_equiv
          (Module.Basis.finTwoProd (AdjoinRoot g))).symm A)) := by
  letI : Module.Finite (AdjoinRoot g) (AdjoinRoot g × AdjoinRoot g) := inferInstance
  letI : Module.Finite K (AdjoinRoot g × AdjoinRoot g) := inferInstance
  let C := frameBlockCoords ε ({i, j} : Finset (Fin s))
  let Ci := frameBlockCoords ε ({i} : Finset (Fin s))
  let Cj := frameBlockCoords ε ({j} : Finset (Fin s))
  let N : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot g) :=
    (Matrix.SpecialLinearGroup.toLin_equiv
      (Module.Basis.finTwoProd (AdjoinRoot g))).symm A
  let B : _root_.SpecialLinearGroup K (AdjoinRoot g × AdjoinRoot g) :=
    CFSG.LinearAlgebra.RootGroupSL.restrictSL (E := AdjoinRoot g)
      (VJ := AdjoinRoot g × AdjoinRoot g) K A
  have hBC : pairSLHom (g := g) ε hij B ∈ CALinearPlane.coordBlockSL K C := by
    rw [← range_pairSLHom (g := g) ε hij]
    exact ⟨B, rfl⟩
  have hN : Matrix.SpecialLinearGroup.toLin_equiv
      (Module.Basis.finTwoProd (AdjoinRoot g)) N = A := by
    exact Equiv.apply_symm_apply _ A
  apply Subtype.ext
  ext p q
  by_cases hqC : q ∈ C
  · let x : ↥C := ⟨q, hqC⟩
    rw [matrix_entry_pairSLHom_of_mem_pair (g := g) ε hij B x p,
      matrix_entry_theta_pairEmbed_of_mem_pair (g := g) ε hij N x p]
    have hq_union : x.1 ∈ Ci ∪ Cj := by
      have h := hqC
      rw [show C = Ci ∪ Cj from frameBlockCoords_pair_eq_union hij] at h
      exact h
    rcases Finset.mem_union.mp hq_union with hqCi | hqCj
    · obtain ⟨a, hq_eq, hq_basis⟩ :=
        pairBasis_apply_of_mem_singleton_left (g := g) ε hij x hqCi
      have hB : B (pairBasis (g := g) ε hij (C.equivFin x)) =
          A (pairBasis (g := g) ε hij (C.equivFin x)) := rfl
      have hact : blockAct (r := r) g (pairEmbed hij N)
          (pairFrame (g := g) ε i j
            (pairBasis (g := g) ε hij (C.equivFin x))) =
          pairFrame (g := g) ε i j
            (A (pairBasis (g := g) ε hij (C.equivFin x))) := by
        rw [hq_basis]
        rw [blockAct_pairEmbed_pairFrame_zero (g := g) ε hij N a]
        rw [show (Matrix.SpecialLinearGroup.toLin_equiv
            (Module.Basis.finTwoProd (AdjoinRoot g)) N) = A from hN]
      rw [hB, hact]
    · obtain ⟨a, hq_eq, hq_basis⟩ :=
        pairBasis_apply_of_mem_singleton_right (g := g) ε hij x hqCj
      have hB : B (pairBasis (g := g) ε hij (C.equivFin x)) =
          A (pairBasis (g := g) ε hij (C.equivFin x)) := rfl
      have hact : blockAct (r := r) g (pairEmbed hij N)
          (pairFrame (g := g) ε i j
            (pairBasis (g := g) ε hij (C.equivFin x))) =
          pairFrame (g := g) ε i j
            (A (pairBasis (g := g) ε hij (C.equivFin x))) := by
        rw [hq_basis]
        rw [blockAct_pairEmbed_pairFrame_one (g := g) ε hij N a]
        rw [show (Matrix.SpecialLinearGroup.toLin_equiv
            (Module.Basis.finTwoProd (AdjoinRoot g)) N) = A from hN]
      rw [hB, hact]
  · rw [matrix_entry_theta_pairEmbed_of_not_mem_pair (g := g) ε hij N hqC p]
    exact (CALinearPlane.mem_coordBlockSL_iff.mp hBC) p q (Or.inr hqC)

theorem coordBlockSL_frameBlockCoords_pair_eq_sup {K : Type} [Field K] {g : K[X]}
    [Fact (Irreducible g)] {n s r : ℕ}
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) {i j : Fin s} (hij : i ≠ j)
    (hdeg : 2 ≤ (rootPB g).dim) :
    CALinearPlane.coordBlockSL K (frameBlockCoords ε ({i, j} : Finset (Fin s))) =
      CALinearPlane.coordBlockSL K (frameBlockCoords ε ({i} : Finset (Fin s))) ⊔
        CALinearPlane.coordBlockSL K (frameBlockCoords ε ({j} : Finset (Fin s))) ⊔
          (CALinearPlane.coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))).map
            (theta g ε) := by
  letI : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  classical
  let C := frameBlockCoords ε ({i, j} : Finset (Fin s))
  let Ci := frameBlockCoords ε ({i} : Finset (Fin s))
  let Cj := frameBlockCoords ε ({j} : Finset (Fin s))
  let H : Subgroup (_root_.SpecialLinearGroup K (AdjoinRoot g × AdjoinRoot g)) :=
    (CALinearPlane.coordBlockSL K Ci ⊔ CALinearPlane.coordBlockSL K Cj ⊔
      (CALinearPlane.coordBlockSL (AdjoinRoot g) ({i, j} : Finset (Fin s))).map
        (theta g ε)).comap (pairSLHom (g := g) ε hij)
  have hpair_mem : ∀ N : Matrix.SpecialLinearGroup (Fin 2) (AdjoinRoot g),
      pairEmbed hij N ∈ CALinearPlane.coordBlockSL (AdjoinRoot g)
        ({i, j} : Finset (Fin s)) := by
    intro N
    rw [CALinearPlane.mem_coordBlockSL_iff]
    intro a b hab
    rw [pairEmbed_apply_of_notMem hij N hab]
    simp [Matrix.one_apply]
  have htop : H = ⊤ := by
    apply eq_top_of_blockSLk_and_restrictSL (k := K) (E := AdjoinRoot g)
    · simpa [(rootPB g).finrank] using hdeg
    · rintro _ ⟨A, rfl⟩
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
        (pairSLHom_blockSLk_mem_left (g := g) ε hij A))
    · rintro _ ⟨A, hA, rfl⟩
      obtain ⟨A0, rfl⟩ := hA
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (pairSLHom_blockSLk_prodComm_mem_right (g := g) ε hij A0))
    · rintro _ ⟨A, rfl⟩
      rw [Subgroup.mem_comap]
      rw [pairSLHom_restrictSL_eq_theta_pairEmbed (g := g) ε hij A]
      exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem (theta g ε)
        (hpair_mem ((Matrix.SpecialLinearGroup.toLin_equiv
          (Module.Basis.finTwoProd (AdjoinRoot g))).symm A)))
  refine le_antisymm ?_ ?_
  · rw [← range_pairSLHom (g := g) ε hij]
    rintro y ⟨x, rfl⟩
    have hxH : x ∈ H := by rw [htop]; exact Subgroup.mem_top x
    exact hxH
  · refine sup_le ?_ ?_
    · refine sup_le ?_ ?_
      · intro g hg
        rw [CALinearPlane.mem_coordBlockSL_iff] at hg ⊢
        intro p q hpq
        exact hg p q (by
          rcases hpq with hp | hq
          · exact Or.inl (fun hpCi => hp (frameBlockCoords_singleton_subset_left hij hpCi))
          · exact Or.inr (fun hqCi => hq (frameBlockCoords_singleton_subset_left hij hqCi)))
      · intro g hg
        rw [CALinearPlane.mem_coordBlockSL_iff] at hg ⊢
        intro p q hpq
        exact hg p q (by
          rcases hpq with hp | hq
          · exact Or.inl (fun hpCj => hp (frameBlockCoords_singleton_subset_right hij hpCj))
          · exact Or.inr (fun hqCj => hq (frameBlockCoords_singleton_subset_right hij hqCj)))
    · rintro _ ⟨W, hW, rfl⟩
      have hWblock : W ∈ blockSpecialLinear (K := AdjoinRoot g)
          ({i, j} : Finset (Fin s)) := by
        rw [mem_blockSpecialLinear]
        intro a b hab
        simpa [Matrix.one_apply] using
          (CALinearPlane.mem_coordBlockSL_iff.mp hW) a b hab
      rw [← range_pairEmbed hij] at hWblock
      obtain ⟨N, rfl⟩ := hWblock
      have heq : pairSLHom (g := g) ε hij
          ((CFSG.LinearAlgebra.RootGroupSL.restrictSL (E := AdjoinRoot g)
            (VJ := AdjoinRoot g × AdjoinRoot g) K)
            (Matrix.SpecialLinearGroup.toLin_equiv
              (Module.Basis.finTwoProd (AdjoinRoot g)) N)) =
          theta g ε (pairEmbed hij N) := by
        have h := pairSLHom_restrictSL_eq_theta_pairEmbed (g := g) ε hij
          (Matrix.SpecialLinearGroup.toLin_equiv
            (Module.Basis.finTwoProd (AdjoinRoot g)) N)
        erw [Equiv.symm_apply_apply] at h
        exact h
      rw [← heq, ← range_pairSLHom (g := g) ε hij]
      exact ⟨_, rfl⟩

end CoordSL

end CFSG.StandardType

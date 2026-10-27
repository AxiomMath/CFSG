module

public import CFSG.RankThree.PartOne.KE6.Phi3Lattice
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
public import CFSG.RankThree.PartOne.KE6.Phi3Torus

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus)
open scoped Matrix

theorem torusRootKernel_smul_stable {L : Type} [Field L] [IsAlgClosed L] {Fr : L →+* L}
    {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {x : ModGL Tag.E6 L}
    (hx : x ∈ twistedTorus (phi3N L) Fr) :
    ∀ α ∈ torusRootKernel x, e6T3W • α ∈ torusRootKernel x := by
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
  have hbker : b ∈ (monomialHom (G := Lˣ) (phi3Matrix q)ᵀ).ker :=
    (mem_twistedTorus_rootDiagUnit_iff3 hFr b).1 (by rw [← hb]; exact hx)
  intro α hα
  rw [hb, torusRootKernel_rootDiagUnit] at hα ⊢
  refine ⟨IsRoot.smul hα.1 e6T3W, ?_⟩
  have h := (mem_ker_monomialHom_iff_forall (phi3Matrix q) b).1 hbker α
  rw [rootChar_phi3Matrix_mulVec, hα.2, one_pow, inv_one, mul_one] at h
  exact h

theorem smul_single_apply_eq_lget {T : WeylGroup Tag.E6} {L : List (List ℤ)}
    (hL : weylMatrix T = toMat Tag.E6.rank L) (i j : Fin Tag.E6.rank) :
    (T • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i = lget L i j := by
  rw [← weylMatrix_apply, hL]
  rfl

theorem exists_smul_pair_eq (S : Finset (Fin Tag.E6.rank))
    (hS : S = {1, 3} ∨ S = {2, 3} ∨ S = {3, 4} ∨ S = {4, 5}) :
    ∃ w : WeylGroup Tag.E6,
      (w • ·) '' parabolicRoots Tag.E6 (↑S : Set (Fin Tag.E6.rank)) =
        parabolicRoots Tag.E6 support13 := by
  have hsupp : ∀ i, i ∈ support13 ↔ (i = 0 ∨ i = 2) := fun i => by
    simp only [support13, Set.mem_insert_iff, Set.mem_singleton_iff]
    rfl
  rcases hS with rfl | rfl | rfl | rfl
  · refine ⟨(coxeterSystem Tag.E6).wordProd (e6Word [3, 2, 1, 3, 0, 2]), ?_⟩
    refine image_smul_parabolicRoots_eq (P := fun i => i = 1 ∨ i = 3) (P' := fun i => i = 0 ∨ i = 2)
      (fun i => by simp) hsupp ?_ ?_
    · simp only [wordProd_e6Word_smul]
      decide +kernel
    · simp only [wordProd_e6Word_smul]
      decide +kernel
  · refine ⟨(coxeterSystem Tag.E6).wordProd (e6Word [3, 2, 0]), ?_⟩
    refine image_smul_parabolicRoots_eq (P := fun i => i = 2 ∨ i = 3) (P' := fun i => i = 0 ∨ i = 2)
      (fun i => by simp) hsupp ?_ ?_
    · simp only [wordProd_e6Word_smul]
      decide +kernel
    · simp only [wordProd_e6Word_smul]
      decide +kernel
  · refine ⟨(coxeterSystem Tag.E6).wordProd (e6Word [3, 4, 2, 3, 0, 2]), ?_⟩
    refine image_smul_parabolicRoots_eq (P := fun i => i = 3 ∨ i = 4) (P' := fun i => i = 0 ∨ i = 2)
      (fun i => by simp) hsupp ?_ ?_
    · simp only [wordProd_e6Word_smul]
      decide +kernel
    · simp only [wordProd_e6Word_smul]
      decide +kernel
  · refine ⟨(coxeterSystem Tag.E6).wordProd (e6Word [3, 4, 5, 2, 3, 4, 0, 2, 3]), ?_⟩
    refine image_smul_parabolicRoots_eq (P := fun i => i = 4 ∨ i = 5) (P' := fun i => i = 0 ∨ i = 2)
      (fun i => by simp) hsupp ?_ ?_
    · simp only [wordProd_e6Word_smul]
      decide +kernel
    · simp only [wordProd_e6Word_smul]
      decide +kernel


theorem phi3_kernel_types {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (z : Fin Tag.E6.rank → ZMod p) (hz : z ≠ 0) (c : ZMod p)
    (hw : (dualMatrix (ZMod p) e6T3W).mulVec z = c • z) :
    rootKernel z = ∅ ∨
      (∃ w : WeylGroup Tag.E6, (w • ·) '' rootKernel z = parabolicRoots Tag.E6 support13) ∨
      (∃ w : WeylGroup Tag.E6, (w • ·) '' rootKernel z = parabolicRoots Tag.E6 supportA2A2) ∨
      (∃ w : WeylGroup Tag.E6, (w • ·) '' rootKernel z =
        parabolicRoots Tag.E6 {i : Fin Tag.E6.rank | i ≠ 0 ∧ i ≠ 5}) := by
  obtain ⟨u, S, hS, hker, -⟩ := e6T3_classification hp5 z hz c hw
  have hS' : S = ∅ ∨ S = {0, 2} ∨ S = {1, 3} ∨ S = {2, 3} ∨ S = {3, 4} ∨ S = {4, 5} ∨
      S = {0, 2, 4, 5} ∨ S = {1, 2, 3, 4} := by
    simpa [e6T3Supports] using hS
  have hstd : ∀ T : Finset (Fin Tag.E6.rank), (T = {1, 3} ∨ T = {2, 3} ∨ T = {3, 4} ∨ T = {4, 5}) →
      S = T → ∃ w : WeylGroup Tag.E6,
        (w • ·) '' rootKernel z = parabolicRoots Tag.E6 support13 := by
    intro T hT hST
    obtain ⟨w, hw⟩ := exists_smul_pair_eq T hT
    refine ⟨w * u, ?_⟩
    have : (fun x : Fin Tag.E6.rank → ℤ => (w * u) • x) =
        (fun x : Fin Tag.E6.rank → ℤ => w • x) ∘ (fun x : Fin Tag.E6.rank → ℤ => u • x) := by
      funext x
      simp [mul_smul]
    rw [this, Set.image_comp, hker, hST, hw]
  rcases hS' with rfl | rfl | h | h | h | h | rfl | rfl
  · left
    have : (u • ·) '' rootKernel z = ∅ := by
      rw [hker]
      refine Set.eq_empty_of_forall_notMem fun α hα => ?_
      exact IsRoot.ne_zero hα.1 (funext fun i => hα.2 i (by simp))
    exact Set.image_eq_empty.1 this
  · right; left
    refine ⟨u, ?_⟩
    rw [hker]
    congr 1
    ext i
    simp only [Finset.coe_insert, Finset.coe_singleton, support13, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rfl
  · right; left
    exact hstd {1, 3} (Or.inl rfl) h
  · right; left
    exact hstd {2, 3} (Or.inr (Or.inl rfl)) h
  · right; left
    exact hstd {3, 4} (Or.inr (Or.inr (Or.inl rfl))) h
  · right; left
    exact hstd {4, 5} (Or.inr (Or.inr (Or.inr rfl))) h
  · right; right; left
    refine ⟨u, ?_⟩
    rw [hker]
    congr 1
    ext i
    simp only [supportA2A2, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rfl
  · right; right; right
    refine ⟨u, ?_⟩
    rw [hker]
    congr 1
    ext i
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_ofPred_eq]
    revert i
    decide +kernel

end CFSG.RankThree.PartOne.KE6


module

public import CFSG.Sporadic.Schreier.LySevenCertificate
public import CFSG.Sporadic.Ly.OrbitSpec

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native Matrix
open CFSG.Sporadic.Th (allIn_eq_true)
open CFSG.Sporadic.Th.Native (ap)

@[expose] def asArr : Array (Mat × Mat) := aStarArr (powM 5 111 matB 4)

@[expose] def genArr (j : ℕ) : Array ℕ := restrArr (pairAt asArr (j + 2)).1

@[expose] def valsArr : Array (Array ℕ) := dagArr genArr

@[expose] def lvArr (i : ℕ) : Array (Array ℕ) :=
  ((hLevelGens.getD i []).map fun k => valsArr.getD k id7).toArray

@[expose] def vArr : Mat := evalWordM seedM (seedMInv (powM 5 111 matB 4)) transporterWord

@[expose] def tArr : Mat := mulM 5 111 (mulM 5 111 (invM 5 111 vArr) matA) vArr

@[expose] def conjTree : Array (Array ℕ) × Array ℕ × Array ℕ :=
  conjBFS (restrArr tArr) (hGenPairs asArr) 406875

structure SevenFacts : Prop where
  b4 : mulM 5 111 matB (powM 5 111 matB 4) = idM 111
  size : asArr.size = 7
  inv : invPairsOK asArr = true
  gens : ∀ j, 2 ≤ j → j < 7 →
    actKey (frTable (pairAt asArr j).1) bpRootKey = some bpRootKey ∧
    stabOK (pairAt asArr j).1 = true
  valsSize : valsArr.size = hDag.size
  dagLocal : dagLocalOK genArr valsArr = true
  dagInv : dagInvOK valsArr = true
  dagOrder : ∀ k < hDag.size, hDag[k]!.1 = 0 ∨
    (hDag[k]!.2.1 < k ∧ (hDag[k]!.1 = 1 ∨ hDag[k]!.2.2 < k))
  fix1 : levelFixOK (lvArr 1) 1 = true
  fix2 : levelFixOK (lvArr 2) 2 = true
  tree0 : vecTreeOK (stdVec 0) (lvArr 0) (vecBFS (stdVec 0) (lvArr 0)) = true
  size0 : (vecBFS (stdVec 0) (lvArr 0)).1.size = 15624
  tree1 : vecTreeOK (stdVec 1) (lvArr 1) (vecBFS (stdVec 1) (lvArr 1)) = true
  size1 : (vecBFS (stdVec 1) (lvArr 1)).1.size = 3125
  tree2 : vecTreeOK (stdVec 2) (lvArr 2) (vecBFS (stdVec 2) (lvArr 2)) = true
  size2 : (vecBFS (stdVec 2) (lvArr 2)).1.size = 120
  vInv : mulM 5 111 vArr (invM 5 111 vArr) = idM 111
  hpInv : ∀ p ∈ hGenPairs asArr, mul7 p.1 p.2 = id7
  conj : conjTreeOK (restrArr tArr) (hGenPairs asArr) conjTree = true
  conjSize : 406875 ≤ conjTree.1.size

theorem sevenFacts : SevenFacts := by
  have h := ly_seven_certificate
  unfold sevenCertificate at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨h, hconjSize⟩ := h
  obtain ⟨h, hconj⟩ := h
  obtain ⟨h, hhp⟩ := h
  obtain ⟨h, hvInv⟩ := h
  obtain ⟨h, hsize2⟩ := h
  obtain ⟨h, htree2⟩ := h
  obtain ⟨h, hsize1⟩ := h
  obtain ⟨h, htree1⟩ := h
  obtain ⟨h, hsize0⟩ := h
  obtain ⟨h, htree0⟩ := h
  obtain ⟨h, hfix2⟩ := h
  obtain ⟨h, hfix1⟩ := h
  obtain ⟨h, hord⟩ := h
  obtain ⟨h, hdagInv⟩ := h
  obtain ⟨h, hdagLocal⟩ := h
  obtain ⟨h, hvalsSize⟩ := h
  obtain ⟨h, hgens⟩ := h
  obtain ⟨h, hinv⟩ := h
  obtain ⟨hb4, hsize⟩ := h
  refine ⟨hb4, hsize, hinv, fun j h2 h7 => ?_, hvalsSize, hdagLocal, hdagInv, fun k hk => ?_,
    hfix1, hfix2, htree0, hsize0, htree1, hsize1, htree2, hsize2, hvInv, fun p hp => ?_, hconj,
    hconjSize⟩
  · have := (allIn_eq_true.1 hgens) j h2 h7
    rw [Bool.and_eq_true] at this
    exact ⟨option_byteArray_eq_of_beq this.1, this.2⟩
  · have := (allIn_eq_true.1 hord) k (Nat.zero_le _) hk
    simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using this
  · have := (Array.all_eq_true'.1 hhp) p hp
    simpa only [beq_iff_eq] using this

end CFSG.Sporadic.LySchreier

module

public import Certificates.Data.CFSGNative.J3.Check
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.J3

open Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native

structure Facts (D : Data) (c : ℕ) : Prop where
  powA : powRows 80 D.rowsA 2 = J3.Native.idRows 80
  powB : powRows 80 D.rowsB 3 = J3.Native.idRows 80
  powAB : powRows 80 (mulRows 80 D.rowsA D.rowsB) 19 = J3.Native.idRows 80
  orbit : orbitOK 80 D.n D.colsA D.colsB D.pts D.tA D.tB = true
  n_pos : 0 < D.n
  n_lt : D.n < 2 ^ 30
  invA : invOK D.n D.tA (invT D.n D.tA) = true
  invB : invOK D.n D.tB (invT D.n D.tB) = true
  a0 : ap D.tA 0 ≠ 0
  b0 : ap D.tB 0 ≠ 0
  ab0 : ap D.tA (ap D.tB 0) ≠ 0
  basis_size : D.basis.size = 80
  basis_lt : ∀ t < D.basis.size, D.basis[t]! < D.n
  basis_inv : mulRows 80 D.basisInv (D.basis.map fun i => D.pts[i]!) = J3.Native.idRows 80
  slp : CFSG.Sporadic.Fi23.Native.slpOK D.words = true
  words_size : 2 ≤ D.words.size
  word0 : D.words[0]! = [1]
  word1 : D.words[1]! = [2]
  chain : chainOK D.n D.letters D.base D.basis D.qb D.trees c = true
  sizes : orbitSizes D.trees = D.orbSizes
  base_pos : 0 < D.base.size
  base0 : D.base[0]! = 0
  k_pos : 0 < D.subReps.size
  rep0 : D.subReps[0]! = 0
  S_size : D.subTrees.size = D.subReps.size
  S0 : D.subTrees[0]!.pts.size = 1
  subTrees : ∀ j < D.subReps.size,
    treeOK D.n D.subReps[j]! D.subTrees[j]! D.letters D.lv = true
  labs_mem : ∀ p < D.n, D.labs[p]! < D.subReps.size ∧ inTreeB D.subTrees[D.labs[p]!]! p = true
  labs_pts : ∀ j < D.subReps.size, ∀ t < D.subTrees[j]!.pts.size,
    D.labs[ap D.subTrees[j]!.pts t]! = j
  derivs : ∀ c', 1 ≤ c' → c' < D.subReps.size →
    derivOK D.n D.subReps.size D.trees[0]! D.letters D.subReps D.labs c' D.derivs[c']! = true

theorem facts_of_check {D : Data} {c : ℕ} (h : check D c = true) : Facts D c := by
  have h' : matOK D.rowsA D.rowsB = true ∧
      orbitChecks D D.colsA D.colsB D.pts D.tA D.tB = true ∧
      chainChecks D D.letters D.trees c = true ∧
      subChecks D D.letters D.lv D.subTrees D.labs = true ∧
      derivChecks D D.letters D.trees[0]! D.labs = true := by
    unfold check at h
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  obtain ⟨hm, ho, hc, hs, hd⟩ := h'
  simp only [matOK, Bool.and_eq_true, beq_iff_eq] at hm
  simp only [orbitChecks, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq,
    Array.all_eq_true] at ho
  simp only [chainChecks, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  simp only [subChecks, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  obtain ⟨⟨hA, hB⟩, hAB⟩ := hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ho1, ho2⟩, ho3⟩, ho4⟩, ho5⟩, ho6⟩, ho7⟩, ho8⟩, ho9⟩, ho10⟩, ho11⟩ := ho
  obtain ⟨⟨⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩, hc5⟩, hc6⟩ := hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩, hs6⟩, hs7⟩, hs8⟩, hs9⟩ := hs
  refine ⟨hA, hB, hAB, ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho8, ho9, fun t ht => ?_, ho11, hc1,
    hc2, hc3, hc4, hc5, hc6, hs1, hs2, hs3, hs4, hs5, hs6,
    fun j hj => (allIn_eq_true.1 hs7) j (Nat.zero_le _) hj,
    fun p hp => ?_, fun j hj t ht => ?_, fun c' h1 h2 => (allIn_eq_true.1 hd) c' h1 h2⟩
  · rw [getElem!_pos D.basis t ht]
    simpa using ho10 t ht
  · have := (allIn_eq_true.1 hs8) p (Nat.zero_le _) hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 hs9) j (Nat.zero_le _) hj)) t (Nat.zero_le _) ht
    simpa using this

end CFSG.Sporadic.J3

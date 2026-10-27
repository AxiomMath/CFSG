module

public import Certificates.Data.CFSGNative.HS.Cert
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.Sporadic.SmallF2

open Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native

variable (D : VecData)

noncomputable abbrev O : VOrbit := D.orbit ()

noncomputable abbrev R0 : Array Table := regs0 D (O D)

noncomputable abbrev SLP : Array Table × Bool := runSLP D.n D.prog (R0 D)

noncomputable abbrev L : Array Table := lettersOf D.n D.sel (SLP D).1

noncomputable abbrev T : Array Tree := chainTrees D.n (L D) D.base

noncomputable abbrev lv : Array ℕ := levelLetters (L D) D.base 1

noncomputable abbrev S : Array Tree := D.subReps.map fun r => treeBFS D.n r (L D) (lv D)

noncomputable abbrev labs : Array ℕ := labelsOf D.n (S D)

structure BaseFacts : Prop where
  d_pos : 0 < D.d
  d_lt : D.d < 64
  expA_pos : 0 < D.expA
  expB_pos : 0 < D.expB
  powA : powRows D.d D.rowsA D.expA = SmallF2.Native.idRows D.d
  powB : powRows D.d D.rowsB D.expB = SmallF2.Native.idRows D.d
  orbit : vOrbitOK D.d D.n D.colsA D.colsB (O D) = true
  n_lt : D.n < 2 ^ 30
  invA : invOK D.n (O D).alpha (invT D.n (O D).alpha) = true
  invB : invOK D.n (O D).beta (invT D.n (O D).beta) = true
  basis_size : D.basis.size = D.d
  basis_lt : ∀ i < D.basis.size, D.basis[i]! < D.n
  basis_inv : mulRows D.d D.basisInv (D.basis.map fun i => (O D).pts[i]!) = SmallF2.Native.idRows D.d

structure Facts (c : ℕ) : Prop extends BaseFacts D where
  nregs : 2 ≤ D.nregs
  prog : ∀ ins ∈ D.prog, instrLt D.nregs ins = true
  slp : (SLP D).2 = true
  sel : ∀ j < D.sel.size, D.sel[j]! < D.nregs
  chain : chainOK D.n (L D) D.base D.basis D.qb (T D) c = true
  orbSizes : orbitSizes (T D) = D.orbSizes
  siftA : sift (T D) (L D) D.qb D.basis 0 (apT (O D).alpha D.basis) = true
  siftB : sift (T D) (L D) D.qb D.basis 0 (apT (O D).beta D.basis) = true
  base_pos : 0 < D.base.size
  base0 : D.base[0]! = 0
  k_pos : 0 < D.subReps.size
  rep0 : D.subReps[0]! = 0
  S_size : (S D).size = D.subReps.size
  subSizes : ((S D).toList.map fun T => T.pts.size) = D.subSizes
  subTrees : ∀ j < D.subReps.size, treeOK D.n D.subReps[j]! (S D)[j]! (L D) (lv D) = true
  labs_lt : ∀ p < D.n, (labs D)[p]! < D.subReps.size
  labs_mem : ∀ p < D.n, inTreeB (S D)[(labs D)[p]!]! p = true
  labs_pts : ∀ j < D.subReps.size, ∀ t < (S D)[j]!.pts.size, (labs D)[ap (S D)[j]!.pts t]! = j
  ord0 : ordOK D.n D.basis (R0 D)[0]! D.ord0 = true
  ord1 : ordOK D.n D.basis (R0 D)[1]! D.ord1 = true
  ord01 : ordOK D.n D.basis (compT D.n (R0 D)[0]! (R0 D)[1]!) D.ord01 = true

private theorem array_all_lt {a : Array ℕ} {m : ℕ} (h : a.all (· < m) = true) :
    ∀ i < a.size, a[i]! < m := by
  intro i hi
  rw [Array.all_eq_true] at h
  have := h i hi
  rw [getElem!_pos a i hi]
  simpa using this

theorem facts_of_vecCert {c : ℕ} (h : vecCert D c = true) : Facts D c := by
  unfold vecCert baseChecks chainChecks subChecks ordChecks at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at h
  obtain ⟨hd0, hd64, heA, heB, hpA, hpB, horb, hn, hiA, hiB, hbs, hblt, hbinv, hnr, hprog, hslp,
    hsel, hch, hos, hsa, hsb, hb0, hb00, hk, hr0, hSs, hss, htr, hlab, hpts, ho0, ho1, ho01⟩ := h
  refine ⟨⟨hd0, hd64, heA, heB, hpA, hpB, horb, hn, hiA, hiB, hbs, array_all_lt hblt, hbinv⟩,
    hnr, ?_, hslp, array_all_lt hsel, hch, hos, hsa, hsb, hb0, hb00, hk, hr0, hSs, hss,
    fun j hj => (allIn_eq_true.1 htr) j (Nat.zero_le _) hj,
    fun p hp => ?_, fun p hp => ?_, fun j hj t ht => ?_, ho0, ho1, ho01⟩
  · intro ins hins
    exact List.all_eq_true.1 hprog ins hins
  · have := (allIn_eq_true.1 hlab) p (Nat.zero_le _) hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · have := (allIn_eq_true.1 hlab) p (Nat.zero_le _) hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 hpts) j (Nat.zero_le _) hj)) t (Nat.zero_le _) ht
    simpa using this

end CFSG.Sporadic.SmallF2

module

public import Certificates.Data.CFSGNative.McL.VecOrbit
public import CFSG.F3.SepSpec
public import CFSG.F3.ConjSpec

public section

namespace CFSG.Sporadic.VecOrbit

open CFSG.F3.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Native Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem powM_size (d : ℕ) (M : Array V) (e : ℕ) : (powM d M e).size = d := by
  induction e with
  | zero => exact idM_size d
  | succ e ih => rw [powM, mul_size, ih]

theorem rowsWF_powM {d : ℕ} {M : Array V} (hM : RowsWF M) (e : ℕ) : RowsWF (powM d M e) := by
  induction e with
  | zero => exact RowsWF.idM d
  | succ e ih => exact RowsWF.mul _ d ih hM

theorem toMat_powM {d : ℕ} {M : Array V} (hM : RowsWF M) (e : ℕ) :
    toMat d (powM d M e) = toMat d M ^ e := by
  induction e with
  | zero => rw [pow_zero]; exact toMat_idM d
  | succ e ih =>
    rw [CFSG.F3.Native.powM, toMat_mul (powM_size d M e) (rowsWF_powM hM e) hM, ih, pow_succ]

theorem not_eqM_of_ne {d : ℕ} {X Y : Array V} (hX : X.size = d) (h : eqM d X Y = false) :
    canonM d X = true → canonM d Y = true → toMat d X ≠ toMat d Y := by
  intro hXc hYc he
  have := eq_of_canonM hXc hYc he
  subst this
  unfold eqM at h
  simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
  rcases h with (h | h) | h
  · exact h hX
  · exact h hX
  · rw [Nat.all_eq_finRange_all, List.all_eq_false] at h
    obtain ⟨i, -, hi⟩ := h
    simp [V.beq] at hi

structure VecFacts (d : ℕ) (A B : Array V) (O : VOrbit) : Prop where
  size_pos : 0 < O.pts.size
  size_lt : O.pts.size < 2 ^ 32
  wf : ∀ k < O.pts.size, (O.pts[k]!).wf = true
  alpha : ∀ k < O.pts.size, ap O.alpha k < O.pts.size ∧
    vecOf d O.pts[ap O.alpha k]! = (toMat d A).mulVec (vecOf d O.pts[k]!)
  beta : ∀ k < O.pts.size, ap O.beta k < O.pts.size ∧
    vecOf d O.pts[ap O.beta k]! = (toMat d B).mulVec (vecOf d O.pts[k]!)
  inj : ∀ i < O.pts.size, ∀ j < O.pts.size, vecOf d O.pts[i]! = vecOf d O.pts[j]! → i = j
  tree : ∀ k < O.pts.size, 0 < k → ap O.par k < k ∧
    ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨ (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k))

theorem vecOf_eq_of_beq {d : ℕ} {a b : V} (h : a.beq b = true) : vecOf d a = vecOf d b := by
  funext j
  exact V.val_ext h j.val

theorem vecOf_comb_transpose {d : ℕ} (M : Array V) {v : V} (hv : v.wf = true) :
    vecOf d (comb d (transpose d M) v) = (toMat d M).mulVec (vecOf d v) :=
  vecOf_mulVecM M hv

theorem vecOrbitOK_facts {d : ℕ} {A B : Array V} {O : VOrbit} {c : ℕ}
    (h : vecOrbitOK d (transpose d A) (transpose d B) O c = true) : VecFacts d A B O := by
  unfold vecOrbitOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hpos, hlt⟩, hall⟩ := h
  set pos : V → ℕ := fun X => (vindexOf O.pts).getD (vkey X) O.pts.size
  have hat := parAll_eq_true hall
  have hk : ∀ k < O.pts.size, (O.pts[k]!).canon d = true ∧ pos O.pts[k]! = k ∧
      ap O.alpha k < O.pts.size ∧
      (comb d (transpose d A) O.pts[k]!).beq O.pts[ap O.alpha k]! = true ∧
      ap O.beta k < O.pts.size ∧
      (comb d (transpose d B) O.pts[k]!).beq O.pts[ap O.beta k]! = true ∧
      (k = 0 ∨ (ap O.par k < k ∧ ((ap O.lab k = 1 ∧ ap O.alpha (ap O.par k) = k) ∨
        (ap O.lab k = 2 ∧ ap O.beta (ap O.par k) = k)))) := by
    intro k hk
    have := hat k hk
    simp only [vecCheckAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true]
      at this
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := this
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hwf : ∀ k < O.pts.size, (O.pts[k]!).wf = true := by
    intro k hk'
    have := (hk k hk').1
    unfold V.canon at this
    simp only [Bool.and_eq_true] at this
    exact this.1.1
  refine ⟨hpos, hlt, hwf, ?_, ?_, ?_, ?_⟩
  · intro k hk'
    obtain ⟨-, -, ha, he, -⟩ := hk k hk'
    refine ⟨ha, ?_⟩
    rw [← vecOf_eq_of_beq he, vecOf_comb_transpose A (hwf k hk')]
  · intro k hk'
    obtain ⟨-, -, -, -, hb, he, -⟩ := hk k hk'
    refine ⟨hb, ?_⟩
    rw [← vecOf_eq_of_beq he, vecOf_comb_transpose B (hwf k hk')]
  · intro i hi j hj hij
    have hci := (hk i hi).1
    have hcj := (hk j hj).1
    unfold V.canon at hci hcj
    have e : O.pts[i]! = O.pts[j]! := V.eq_of_canon (d := d) hci hcj fun r hr => by
      have := congrFun hij ⟨r, hr⟩
      simpa only [vecOf] using this
    rw [← (hk i hi).2.1, ← (hk j hj).2.1, e]
  · intro k hk' hk0
    rcases (hk k hk').2.2.2.2.2.2 with h0 | h1
    · omega
    · exact h1

theorem eq_one_of_basisOK {d : ℕ} {S Tinv : Array V} (h : basisOK d S Tinv = true)
    (g : Matrix (Fin d) (Fin d) (ZMod 3))
    (hg : ∀ i < d, g.mulVec (vecOf d S[i]!) = vecOf d S[i]!) : g = 1 := by
  unfold basisOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, hSwf⟩, hTwf⟩, hTs⟩, hTS⟩ := h
  set T := toMat d S
  have hTinv := toMat_eq_of_eqM hTS
  rw [toMat_mul hTs (rowsWF_of_wfM hTwf) (rowsWF_of_wfM hSwf), toMat_idM] at hTinv
  have hgT : g * Tᵀ = Tᵀ := by
    ext r i
    rw [Matrix.mul_apply, Matrix.transpose_apply]
    have := congrFun (hg i.val i.isLt) r
    rw [mulVec, dotProduct] at this
    simpa [T, toMat_apply, vecOf] using this
  have hright : Tᵀ * (toMat d Tinv)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hTinv, Matrix.transpose_one]
  calc g = g * (Tᵀ * (toMat d Tinv)ᵀ) := by rw [hright, mul_one]
    _ = (g * Tᵀ) * (toMat d Tinv)ᵀ := by rw [mul_assoc]
    _ = 1 := by rw [hgT, hright]

end CFSG.Sporadic.VecOrbit

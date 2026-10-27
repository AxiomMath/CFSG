module

import all CFSG.RankThree.PartTwo.Sec21.Hering2119SShareK
public import CFSG.RankThree.PartTwo.Sec21.Hering2119KCore

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Matrix

structure NormEl (g g' : M4) : Prop where
  mul_inv : g * g' = 1
  inv_mul : g' * g = 1
  symp : ∀ x y, omega4 (g.mulVec x) (g.mulVec y) = omega4 x y
  fixA : ∀ v, inA v → g.mulVec v = v

theorem NormEl.symm {g g' : M4} (h : NormEl g g') : NormEl g' g := by
  refine ⟨h.inv_mul, h.mul_inv, ?_, ?_⟩
  · intro x y
    have := h.symp (g'.mulVec x) (g'.mulVec y)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h.mul_inv, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
    exact this.symm
  · intro v hv
    have := h.fixA v hv
    calc g'.mulVec v = g'.mulVec (g.mulVec v) := by rw [this]
      _ = v := by rw [Matrix.mulVec_mulVec, h.inv_mul, Matrix.one_mulVec]

theorem NormEl.conj_apply {g g' : M4} (X : M4) (v : V4) :
    (g * X * g').mulVec v = g.mulVec (X.mulVec (g'.mulVec v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem NormEl.conj_conj {g g' : M4} (h : NormEl g g') (X : M4) : g' * (g * X * g') * g = X := by
  calc g' * (g * X * g') * g = (g' * g) * X * (g' * g) := by simp only [mul_assoc]
    _ = X := by rw [h.inv_mul, one_mul, mul_one]

theorem NormEl.inF {g g' : M4} (h : NormEl g g') {a : V4} (ha : inA a) {X : M4} {w : V4}
    (hw : InF a X w) : InF a (g * X * g') (g.mulVec w) := by
  obtain ⟨c, k, hk1, hk2, hwe⟩ := hw
  have hga := h.fixA a ha
  refine ⟨c, g.mulVec k, ?_, ?_, ?_⟩
  · have hinv : g'.mulVec (g.mulVec k) = k := by
      rw [Matrix.mulVec_mulVec, h.inv_mul, Matrix.one_mulVec]
    rw [NormEl.conj_apply, hinv, hk1]
  · have := h.symp a k
    rw [hga, hk2] at this
    exact this
  · rw [hwe, Matrix.mulVec_add, Matrix.mulVec_smul, hga]

theorem NormEl.inF' {g g' : M4} (h : NormEl g g') {a : V4} (ha : inA a) {X : M4} {v : V4}
    (hv : InF a (g * X * g') v) : InF a X (g'.mulVec v) := by
  have := h.symm.inF ha hv
  rwa [h.conj_conj] at this

theorem NormEl.conj_mul3 {g g' : M4} (h : NormEl g g') (A B C : M4) :
    (g * A * g') * (g * B * g') * (g * C * g') = g * (A * B * C) * g' := by
  calc (g * A * g') * (g * B * g') * (g * C * g')
      = g * A * (g' * g) * B * (g' * g) * C * g' := by simp only [mul_assoc]
    _ = g * (A * B * C) * g' := by rw [h.inv_mul]; simp only [mul_one, mul_assoc]

theorem NormEl.conj_mul2 {g g' : M4} (h : NormEl g g') (A B : M4) :
    (g * A * g') * (g * B * g') = g * (A * B) * g' := by
  calc (g * A * g') * (g * B * g') = g * A * (g' * g) * B * g' := by simp only [mul_assoc]
    _ = g * (A * B) * g' := by rw [h.inv_mul]; simp only [mul_one, mul_assoc]

theorem NormEl.conj_one {g g' : M4} (h : NormEl g g') : g * 1 * g' = 1 := by
  rw [mul_one, h.mul_inv]

theorem NormEl.conj_inj {g g' : M4} (h : NormEl g g') {A B : M4} (hAB : g * A * g' = g * B * g') :
    A = B := by
  have := congrArg (fun Z => g' * Z * g) hAB
  rwa [h.conj_conj, h.conj_conj] at this

theorem NormEl.isItem {g g' : M4} (h : NormEl g g') {a : V4} (ha : inA a) {X T : M4}
    (hI : IsItem a X T) : IsItem a (g * X * g') (g * T * g') where
  symp x y := by
    rw [NormEl.conj_apply, NormEl.conj_apply, h.symp, hI.symp, h.symm.symp]
  ne_one := by
    intro h1
    apply hI.ne_one
    apply h.conj_inj
    rw [h1, h.conj_one]
  cube := by
    rw [h.conj_mul3, hI.cube, h.conj_one]
  noFix v hv hne hfix := by
    have h1 : g'.mulVec v = v := h.symm.fixA v hv
    rw [NormEl.conj_apply, h1] at hfix
    apply hI.noFix v hv hne
    have key1 : ∀ w, g'.mulVec (g.mulVec w) = w := fun w => by
      rw [Matrix.mulVec_mulVec, h.inv_mul, Matrix.one_mulVec]
    have h2 : X.mulVec v = g'.mulVec v := by
      calc X.mulVec v = g'.mulVec (g.mulVec (X.mulVec v)) := (key1 _).symm
        _ = g'.mulVec v := by rw [hfix]
    rw [h2, h1]
  presF v hv := by
    have h1 := h.inF' ha hv
    have h2 := hI.presF _ h1
    have h3 := h.inF ha h2
    rw [NormEl.conj_apply]
    exact h3
  sq := by
    rw [h.conj_mul2, hI.sq, h.conj_one]
  mult x y := by
    rw [NormEl.conj_apply, NormEl.conj_apply, h.symp, hI.mult, h.symm.symp]
  fixa := by
    rw [NormEl.conj_apply, h.symm.fixA a ha, hI.fixa, h.fixA a ha]
  neg v hv := by
    have key1 : ∀ w, g'.mulVec (g.mulVec w) = w := fun w => by
      rw [Matrix.mulVec_mulVec, h.inv_mul, Matrix.one_mulVec]
    have key2 : ∀ w, g.mulVec (g'.mulVec w) = w := fun w => by
      rw [Matrix.mulVec_mulVec, h.mul_inv, Matrix.one_mulVec]
    have hv' : g.mulVec (X.mulVec (g'.mulVec v)) = v :=
      (NormEl.conj_apply (g := g) (g' := g') X v).symm.trans hv
    have h1 : X.mulVec (g'.mulVec v) = g'.mulVec v := by
      calc X.mulVec (g'.mulVec v) = g'.mulVec (g.mulVec (X.mulVec (g'.mulVec v))) := (key1 _).symm
        _ = g'.mulVec v := by rw [hv']
    rw [NormEl.conj_apply, hI.neg _ h1]
    calc g.mulVec (-(g'.mulVec v)) = -(g.mulVec (g'.mulVec v)) := Matrix.mulVec_neg _ g
      _ = -v := by rw [key2]

theorem inA_lineVec (i : Fin 4) : inA (lineVec i) := by
  fin_cases i <;> simp [inA, lineVec]

@[expose] def umat (s0 s1 s2 : F3) : M4 :=
  !![1, 0, s0, s1; 0, 1, s1, s2; 0, 0, 1, 0; 0, 0, 0, 1]

theorem umat_symp (s0 s1 s2 : F3) (x y : V4) :
    omega4 ((umat s0 s1 s2).mulVec x) ((umat s0 s1 s2).mulVec y) = omega4 x y := by
  simp [omega4, umat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

theorem umat_fixA (s0 s1 s2 : F3) (v : V4) (hv : inA v) : (umat s0 s1 s2).mulVec v = v := by
  obtain ⟨h2, h3⟩ := hv
  ext i
  fin_cases i <;> simp [umat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, h2, h3]

theorem uC_toM (a b c : Nat) : (uC a b c).toM = umat a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uC, umat, M4C.toM]

end CFSG.RankThree.PartTwo.Sec21.Hering2119S

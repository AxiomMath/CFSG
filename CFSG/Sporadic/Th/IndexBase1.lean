
module


public import CFSG.Sporadic.Th.Plane

@[expose] public section

namespace CFSG.Sporadic.Th

open Native Pointwise

noncomputable instance idxInst : MulAction J (Fin nX) where
  smul g i := by
    classical
    exact if h : OrbitFacts then (planeEquiv h).symm (g • planeEquiv h i) else i
  one_smul i := by
    classical
    show (if h : OrbitFacts then (planeEquiv h).symm ((1 : J) • planeEquiv h i) else i) = i
    split
    · rw [one_smul, Equiv.symm_apply_apply]
    · rfl
  mul_smul g h i := by
    classical
    show (if hF : OrbitFacts then (planeEquiv hF).symm ((g * h) • planeEquiv hF i) else i) =
      (if hF : OrbitFacts then (planeEquiv hF).symm (g • planeEquiv hF
        (if hF : OrbitFacts then (planeEquiv hF).symm (h • planeEquiv hF i) else i)) else
        (if hF : OrbitFacts then (planeEquiv hF).symm (h • planeEquiv hF i) else i))
    split
    · rw [Equiv.apply_symm_apply, mul_smul]
    · rfl

section Facts

variable (hF : OrbitFacts)
include hF

theorem planeEquiv_smul
    (g : J) (i : Fin nX) : planeEquiv hF (g • i) = g • planeEquiv hF i := by
  have : (g • i : Fin nX) = (planeEquiv hF).symm (g • planeEquiv hF i) := by
    classical
    show (if h : OrbitFacts then (planeEquiv h).symm (g • planeEquiv h i) else i) = _
    rw [dite_eq_left hF]
  rw [this, Equiv.apply_symm_apply]

theorem planeAt_smul
    (g : J) (i : Fin nX) : planeAt ((g • i : Fin nX) : ℕ) = g • planeAt i := by
  have := congrArg Subtype.val (planeEquiv_smul hF g i)
  simpa [planeEquiv_apply] using this

theorem smul_idx_eq_iff
    (g : J) (i j : Fin nX) : g • i = j ↔ g • planeAt i = planeAt j := by
  constructor
  · rintro rfl
    exact (planeAt_smul hF g i).symm
  · intro h
    apply Fin.ext
    apply planeAt_injective hF _ (g • i).isLt _ j.isLt
    rw [planeAt_smul hF, h]

theorem idx_eq_iff {g : J} {i j : ℕ} (hi : i < nX) (hj : j < nX) :
    idx nX g i = j ↔ g • planeAt i = planeAt j := by
  rw [idx, dite_eq_left hi]
  constructor
  · intro h
    have := (smul_idx_eq_iff hF g ⟨i, hi⟩ ⟨j, hj⟩).1 (Fin.ext h)
    exact this
  · intro h
    exact congrArg Fin.val ((smul_idx_eq_iff hF g ⟨i, hi⟩ ⟨j, hj⟩).2 h)

theorem rep_alpha : Rep nX alphaT a := by
  intro i hi
  rw [alphaT, ap_tblOfBytes _ hi]
  symm
  exact (idx_eq_iff hF hi (hF.αlt i hi)).2 (a_smul_planeAt hF i hi).2

theorem rep_beta : Rep nX betaT b := by
  intro i hi
  rw [betaT, ap_tblOfBytes _ hi]
  symm
  exact (idx_eq_iff hF hi (hF.βlt i hi)).2 (b_smul_planeAt hF i hi).2

end Facts

end CFSG.Sporadic.Th

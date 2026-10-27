module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBResidualLin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]

theorem o8m_card_le_finrank_of_det_ne_zero {m : ℕ} (v : Fin m → V)
    (φ : Fin m → Module.Dual k V) (h : (Matrix.of fun r c => φ r (v c)).det ≠ 0) :
    m ≤ Module.finrank k V := by
  have hE : IsUnit (Matrix.of fun r c => φ r (v c)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have hv :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.linearIndependent_of_pairing v φ hE
  simpa using hv.fintype_card_le_finrank

theorem o8m_card_le_finrank_range_of_det_ne_zero {m : ℕ} (T : V →ₗ[k] V) (v : Fin m → V)
    (φ : Fin m → Module.Dual k V) (h : (Matrix.of fun r c => φ r (T (v c))).det ≠ 0) :
    m ≤ Module.finrank k (LinearMap.range T) := by
  let v' : Fin m → LinearMap.range T :=
    fun c => ⟨T (v c), LinearMap.mem_range_self T (v c)⟩
  let φ' : Fin m → Module.Dual k (LinearMap.range T) :=
    fun r => (φ r).comp (LinearMap.range T).subtype
  have hmat : (Matrix.of fun r c => φ' r (v' c))
      = Matrix.of fun r c => φ r (T (v c)) := by
    ext r c
    rfl
  have hE : IsUnit (Matrix.of fun r c => φ' r (v' c)) := by
    rw [hmat]
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have hv :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.linearIndependent_of_pairing v' φ' hE
  simpa using hv.fintype_card_le_finrank

end CFSG.LocalAnalysis.WeakClosure81

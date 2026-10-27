module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Concl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.ConjBack
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLFlagMat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLTorusForm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLTorusConcl
import CFSG.LocalAnalysis.UniquenessCase.UC22P22m

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open

theorem kAdj_model_sl {k : ℕ} [NeZero k] (hk : 3 ≤ k) {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) {r : ℕ} (hr : Odd r) {t : ↥(StatedSL k K)}
    (ht : t ∈ Hinf (slQAlpha k K) ⊓ slQZero k K) (hord : orderOf t = r) :
    KAdjConcl (Hinf (slQZero k K)) t r n := by
  obtain ⟨s, hs, c, hc0, hc, hdiag⟩ :=
    exists_conj_slTorusDiag (k := k) (by omega) ht (by rw [hord]; exact hr)
  have hord' : orderOf (s * t * s⁻¹) = r := by
    rw [← hord]
    simpa [MulAut.conj_apply] using
      orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective t
  have hordc : orderOf c = r := (orderOf_eq_of_slMat_eq_diagonal hdiag).symm.trans hord'
  exact kAdjConcl_conj s (uc22p22m_le_normalizer_Hinf (slQZero k K) (slU_le_slQZero hs))
    (kAdjConcl_slTorus hk hK hn hr hordc hdiag)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

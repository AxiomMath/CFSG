module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISpSiegel
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSp
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeOrthPieces

public section

namespace CFSG.StandardType.RCKK1IIISp

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.RCKC1 CFSG.Open
open CFSG.LieType.BorelTits CFSG.StandardType.LieKnownR2.Short CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.B113Lie.Sp
open scoped Matrix commutatorElement

lemma rckSpP_spJ_dotProduct_comm {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (u v : Fin n ⊕ Fin n → K) :
    ((spJ n K) *ᵥ u) ⬝ᵥ v = u ⬝ᵥ ((spJ n K) *ᵥ v) := by
  rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, spJ_transpose_char_two]

lemma rckSpP_spAct_eq_of_smul_ofVec_eq {m : ℕ}
    {g : ↥(StatedSp m (GaloisField 2 1))} {u v : Fin m ⊕ Fin m → GaloisField 2 1}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (h : g • SpPoint.ofVec u hu = SpPoint.ofVec v hv) : spAct g u = v := by
  rw [smul_ofVec g u hu] at h
  have hline := congrArg SpPoint.line h
  rw [line_ofVec, line_ofVec] at hline
  have hmem : spAct g u ∈ Submodule.span (GaloisField 2 1) {v} := by
    rw [← hline]; exact Submodule.mem_span_singleton_self _
  obtain ⟨lam, hlam⟩ := Submodule.mem_span_singleton.mp hmem
  have hlam0 : lam ≠ 0 := by
    intro h0
    have hgu : spAct g u ≠ 0 := by
      intro hz
      have hz0 : spAct g (0 : Fin m ⊕ Fin m → GaloisField 2 1) = 0 := by simp [spAct]
      exact hu (spAct_injective g (hz.trans hz0.symm))
    exact hgu (by rw [← hlam, h0, zero_smul])
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    simpa using CFSG.LieType.Catalog.card_galoisField 2 1 (by norm_num)
  have hlam1 : lam = 1 :=
    (CFSG.HardMathSupport.Curtis.Coordinator.eq_zero_or_one_of_card_two hcard lam).resolve_left
      hlam0
  rw [hlam1, one_smul] at hlam
  exact hlam.symm

lemma rckSpP_ofVec_ne {m : ℕ} {u v : Fin m ⊕ Fin m → GaloisField 2 1}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    SpPoint.ofVec u hu ≠ SpPoint.ofVec v hv := by
  intro h
  have h1 : spAct (1 : ↥(StatedSp m (GaloisField 2 1))) u = v :=
    rckSpP_spAct_eq_of_smul_ofVec_eq hu hv (by simpa using h)
  rw [show spAct (1 : ↥(StatedSp m (GaloisField 2 1))) u = u from by simp [spAct]] at h1
  exact huv h1

end CFSG.StandardType.RCKK1IIISp

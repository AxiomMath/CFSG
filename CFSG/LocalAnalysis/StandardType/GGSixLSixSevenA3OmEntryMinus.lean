module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmEntry
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData Multiplicative

section Model


theorem ggSixLSixSevenConjA3At_POmegaMinus_of_bstar (h : GGSixLSixSevenA3BstarInput .POmegaMinus) :
    GGSixLSixSevenConjA3At .POmegaMinus := by
  intro G _ _ p B Bs x L D J n f
  have hBB := h G p B Bs x L D J n f
  rw [show ggU .POmegaMinus n f = ⟨spinGroup (quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
      (minusCoeffs 2 f).2), Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)⟩ from rfl] at hBB ⊢
  intro ψ hctx hC2 hodd hcomp hA
  have hn : 4 ≤ n := hctx.2.2.2.1.1.2.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hirr := minusCoeffs_irr 2 f
  obtain ⟨-, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← PsiDiag.SpinM.center_eq_bot hirr hn]
    exact hker
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus n (GaloisField 2 f) _ _ hn hirr
  exact exists_conj_le_of_model_bstar hctx hnd hT hψinj (AutOm.spinModelMinus hn hirr)
    ⟨AutOm.spinModelMinus_injective hn hirr, AutOm.spinModelMinus_surjective hn hirr⟩
    (fun b hb => PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb))
    hA (hBB ψ hctx hC2 hodd hcomp hA)

end Model

end CFSG.StandardType

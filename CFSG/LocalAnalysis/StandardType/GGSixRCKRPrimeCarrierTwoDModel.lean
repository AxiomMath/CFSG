module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnSpecs
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDModel
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.StandardType CFSG.Assembly.LowTwoRank
open CFSG.StandardType.LieCore
open CFSG.StandardType.S2MathFi1035Pos


theorem rckTwoD_ggU_facts {n g : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) :
    StandardReturnAt (ggU .POmegaMinus n g) g ∧ Finite (ggU .POmegaMinus n g).K ∧
      Group.IsPerfect (ggU .POmegaMinus n g).K ∧
      CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (ggU .POmegaMinus n g).K ∧
      ∃ β ∈ (ggU .POmegaMinus n g).D.roots, GGLongRoot (ggU .POmegaMinus n g).D β := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Or.inl ⟨.POmegaMinus, n, ?_, ?_, rfl⟩
    · simp only [GGPosTag]
      tauto
    · change Nat.Prime 2 ∧ 1 ≤ g ∧ 4 ≤ n
      exact ⟨Nat.prime_two, hg, hn⟩
  · change Finite (spinGroup (quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
    exact CFSG.ClassicalInvolution.RouteD.finite_spinGroup_quadMinus n _ _
  · change Group.IsPerfect (spinGroup (quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
    exact isPerfect_spinGroup_quadMinus hn (minusCoeffs_irr 2 g)
  · change CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit
      (spinGroup (quadMinus n (GaloisField 2 g) (minusCoeffs 2 g).1 (minusCoeffs 2 g).2))
    exact CFSG.SeitzReduction.SeitzQ2.oddCentralSplit_spinMinus hn (minusCoeffs_irr 2 g)
  · exact CFSG.StandardType.RCKK1I.rckExists_longRoot _ (by change 0 < n - 1; omega)

end CFSG.StandardType.RCKRP

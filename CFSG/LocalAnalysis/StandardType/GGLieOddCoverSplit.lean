module

public import CFSG.LocalAnalysis.StandardType.GGLieOddCoverDefs
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapLiftSplit
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftSplit
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitE7
public import CFSG.LieType.Steinberg.CentralExt.F4TwoMultiplier
public import CFSG.LieType.Steinberg.CentralExt.E8TwoOddSplit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianE6
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Cover
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint

public section

namespace CFSG.StandardType.LieOddCover

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.SeitzReduction.UnitaryPilot CFSG.LieType.Universal.Spin

theorem oddCentralSplit_ggU_pos
    {t : StatedLieTag} {n f : ℕ} (ht : GGPosTag t) (hadm : StatedLieAdmissible t n 2 f) :
    CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit (ggU t n f).K := by
  have hf : 1 ≤ f := hadm.2.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold GGPosTag at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    change OddCentralSplit (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))
    exact CFSG.SeitzReduction.LinearPilot.oddCentralSplit_specialLinearGroup
  · have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
      card_galoisField_two_mul 2 f hf
    have hK : ggU .PSU n f = ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * f)) 2 f) n, Unitary.rootDatum hF n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [hK]
    change OddCentralSplit
      (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n)
    exact (CFSG.SeitzReduction.UnitaryPilot.oddCentralSplit_statedSU (F := GaloisField 2 (2 * f))
        (f := f) hF (by have := hadm.2.2.1; omega) hadm.2.2.2).of_mulEquiv
      (Unitary.equivStatedSU (F := GaloisField 2 (2 * f)) (p := 2) (f := f) hF n).symm
  · change OddCentralSplit (CFSG.Open.StatedSp n (GaloisField 2 f))
    exact CFSG.SeitzReduction.SeitzQ2.oddCentralSplit_statedSp n (GaloisField 2 f)
  · have hn : 3 ≤ n := by have := hadm.2.2; omega
    have hK : ggU .POmegaPlus n f = ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
        Spin.plusDatum n (GaloisField 2 f) hn⟩ := by
      simp only [ggU, lieUniversal, hn, ↓reduceDIte]
    rw [hK]
    change OddCentralSplit (spinGroup (Spin.quadPlus n (GaloisField 2 f)))
    exact CFSG.SeitzReduction.SeitzQ2.oddCentralSplit_spinPlus hn (GaloisField 2 f)
  · change OddCentralSplit
      (spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
    exact CFSG.SeitzReduction.SeitzQ2.oddCentralSplit_spinMinus (n := n)
      (by have := hadm.2.2; omega) (minusCoeffs_irr 2 f)
  · change OddCentralSplit (CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 f))
    intro E _ _ π hπ hcen hodd
    exact CFSG.LieType.Steinberg.CentralExt.F4Two.f4_exists_section_of_coprime E π hπ hcen
      (Nat.coprime_two_left.2 hodd)
  · change OddCentralSplit
      ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField 2 f))
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.oddCentralSplit_e6
      (F := GaloisField 2 f)
  · change OddCentralSplit
      ↥(CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 f))
    exact CFSG.SeitzReduction.SeitzQ2.oddCentralSplit_e7MinGroup (GaloisField 2 f)
  · change OddCentralSplit (CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 f))
    intro E _ _ π hπ hcen hodd
    exact CFSG.LieType.Steinberg.CentralExt.E8Two.e8_exists_section_of_coprime E π hπ hcen
      (Nat.coprime_two_left.2 hodd)
  · change OddCentralSplit (CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 f)
    intro E _ _ π hπ hcen hodd
    exact CFSG.StandardType.TwE6DD2.exists_section_sc hf E π hπ hcen
      (Nat.coprime_two_left.2 hodd)

end CFSG.StandardType.LieOddCover

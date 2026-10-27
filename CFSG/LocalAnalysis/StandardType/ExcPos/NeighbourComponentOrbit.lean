module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
import CFSG.LocalAnalysis.StandardType.GGSixTCPSUNbr
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.Dihedral.DihedralFusionPrefixes
import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ratOrbit_eq_of_isQuasisimple_le
    {τ : Tag} {L : Type} [Field L] {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, CFSG.LieType.Steinberg.Adjoint.iform (ρ γ) (ρ δ) =
      CFSG.LieType.Steinberg.Adjoint.iform γ δ)
    {i j : KernelComponent χ} {H : Subgroup (ModGL τ L)} (hH : CFSG.Assembly.IsQuasisimple H)
    (hi : H ≤ rootSpan τ L (LieCore.ratOrbit ρ (componentRoots χ i)))
    (hj : H ≤ rootSpan τ L (LieCore.ratOrbit ρ (componentRoots χ j))) :
    LieCore.ratOrbit ρ (componentRoots χ i) = LieCore.ratOrbit ρ (componentRoots χ j) := by
  by_contra hij
  have hcomm : ⁅H, H⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxy :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.commute_rootSpan_rationalRoots
        hker hform
        (by
          change ¬ LieCore.ratOrbit (⇑ρ) (componentRoots χ i) =
            LieCore.ratOrbit (⇑ρ) (componentRoots χ j)
          exact hij)
        x (hi hx) y (hj hy)
    exact hxy.symm
  have hperf : ⁅H, H⁆ = H :=
    CFSG.StandardType.TableCRes.tcCommutator_self_of_isQuasisimple hH
  have hne : H ≠ ⊥ := CFSG.StandardType.TableCRes.tcNe_bot_of_isQuasisimple hH
  exact hne (hperf.symm.trans hcomm)

end CFSG.StandardType.LieKnownR2.ExcPos

end

module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcVac
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTSolvable
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Tits
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.Sporadic.Schreier.TitsIso
import CFSG.Sporadic.Schreier.TitsOuter
public import Certificates.Certificate10050
public import Certificates.Certificate8117
import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.EmptyFaithful.S1421Defs
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.H13.J4Order
import CFSG.Quasithin.Vol2.Ch11SecAFacts02
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import Certificates.Certificate13659
import Certificates.Certificate13660
import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem ggNbrLSideNoPSL3_twF4der
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGNbrLSideNoPSL3 (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H 0 K)) := by
  intro φ _ hφ1 hφ3 J hJ F _ _ _
  refine ⟨fun _e => ?_⟩
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := by rw [hK]; norm_num
  have hm : CFSG.Blueprint.ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 hK'⟩
  obtain ⟨eD⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hm
  have hφ'3 : MulAut.congr eD φ ^ 3 = 1 := by rw [← map_pow, hφ3, map_one]
  have hφ'1 : MulAut.congr eD φ ≠ 1 := by
    intro h1
    exact hφ1 ((MulAut.congr eD).injective (h1.trans (map_one (MulAut.congr eD)).symm))
  haveI hsolv : Group.IsSolvable ↥(fixSubgroup φ) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isSolvable_fixSubgroup_of_congr eD
      (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isSolvable_fixSubgroup_titsD
        CFSG.Sporadic.Schreier.Tits.titsD_center hφ'3 hφ'1)
  haveI : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJ.1)
  haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2.toNontrivial
  haveI : Nontrivial ↥J := (QuotientGroup.mk_surjective (s := Subgroup.center ↥J)).nontrivial
  exact Group.IsPerfect.not_isSolvable (↥J) inferInstance

end CFSG.StandardType

end

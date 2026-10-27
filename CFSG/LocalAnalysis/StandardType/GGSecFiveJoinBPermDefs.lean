module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinCells
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinSelected
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPositionDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNativeImageDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGNsq2Cited
public import Certificates.Certificate1952
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8032
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13657
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBWeylInfDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal


@[expose] def GGSecFiveJoinBPermAt (S : ℕ → ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSecFivePhanARow p B Bs x L D J →
      ¬ GGSecFiveQTwoCell p B Bs x L D J →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixB M →
        ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 M e →
        ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
          GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
          ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K →
          ∀ (m : ℕ) (eta : ↥Bs ≃* (Fin m → Multiplicative (ZMod p))), 4 ≤ m →
            ∀ (e' : (CoxeterMatrix.B m).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
            GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B m) e' →
            (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull m p →
            (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull m p →
            GGInnerDiagOnLabel (fun p lab => S m p lab) p Bs L →
              GGSecFiveCompat p B x L D J

@[expose] def GGSecFiveJoinBPermUniInput : Prop :=
      GGResXDichotomyInput → GGTCJKnown → GGLabelRigidInput → GGNbrTablePNbrInputNarrow →
    GGForkA8NotReflInput → GGRawInnFieldInput → GGRawInndiagIsoInput →
    GGResNbrFixCentralizesInput → GGTBTorAll → GGTBTorLiftRows → GGNbrSubcomponentInput →
    GGLBalanceInput → GGStdSubPrimeInput → GGTwE6ThreeNbrRankInput → GGTBFixInput →
    GGSecFiveBProperRootInput → GGLabelCenterPCyclicInput → GGInnerDiagMpInput →
    GGNbrInnerWeylInput → GGSecFiveBCoordDExclInput → GGU62OuterDiagInput →
    KnownActualMemberSelectedInput →
      GGSecFiveJoinBPermAt GGSecFiveBPermUniLabel

@[expose] def GGSecFiveJoinBPermLinInput : Prop :=
      GGResXDichotomyInput → GGTCJKnown → GGLabelRigidInput → GGNbrTablePNbrInputNarrow →
    GGForkA8NotReflInput → GGRawInnFieldInput → GGRawInndiagIsoInput →
    GGResNbrFixCentralizesInput → GGTBTorAll → GGTBTorLiftRows → GGNbrSubcomponentInput →
    GGLBalanceInput → GGStdSubPrimeInput → GGTwE6ThreeNbrRankInput → GGTBFixInput →
    GGSecFiveBProperRootInput → GGLabelCenterPCyclicInput → GGInnerDiagMpInput →
    GGNbrInnerWeylInput → GGSecFiveBCoordDExclInput → GGU62OuterDiagInput →
    KnownActualMemberSelectedInput →
      GGSecFiveJoinBPermAt GGSecFiveBPermLinLabel

end CFSG.StandardType

end

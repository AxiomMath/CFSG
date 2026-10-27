module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12E9Data
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12E9Data
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12CoverData
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12HeisData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12CoverData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12ThreeCentralZ2
import CFSG.Foundations
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.Extremal
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec19.Item194Used
import CFSG.RankThree.PartTwo.Sec19.Step1915W
import CFSG.RankThree.PartTwo.Sec19.Step1917ProofDefs
import Certificates.Certificate2201

public section

open CFSG.AGLEmbedding.KFactProofs.M12Cover

namespace CertificateChecks.Batch9682

open CFSG.AGLEmbedding.KFactProofs.M12Cover

private theorem e9_check : m12E9Facts = true := by
  decide +kernel

end CertificateChecks.Batch9682

namespace Certificates

open CertificateChecks

open CFSG.AGLEmbedding.KFactProofs.M12Cover in
theorem certificate9682 : m12E9Facts = true := by
  exact CertificateChecks.Batch9682.e9_check

end Certificates

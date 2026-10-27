module

public import CFSG.Quasithin.H13.NQCoreSChainStmts
public import CFSG.Quasithin.H13.NQCoreUpward
public import CFSG.Quasithin.H13.NQCoreRadicalCentralizer
public import CFSG.Quasithin.H13.NQBlockStmt1317Setup

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem nonquasisimpleRadicalNormalizerWitness_of
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hA7n : NQBlock.SylowNormalizedLocalNormalComponent) (h1323 : Stmt13_1_2_three)
    (hord : U3.FiveQuotientExactOrders) (hO : StmtSCComponentOrbits)
    (hN : StmtSCNormalExclusion) (hP : StmtSCPairedExclusion)
    (h5 : StmtSNRadicalCentralizer) : NQBlock.NonquasisimpleRadicalNormalizerWitness := by
  intro G _ _ T hs hnab hQ hT hX hK
  obtain ⟨K, hKf, hKq⟩ := hK
  have : IsSimpleGroup G := hs
  obtain ⟨L, -, hLmax, hLf, hTL, hLq⟩ :=
    nonquasisimple_maximal_local_of_faithful h37 h38 h1323 hord hnab hQ hX hT hKf hKq
  obtain ⟨⟨p, hp, hp5, hCp⟩, hA, hall⟩ :=
    sylow_normalized_maximal_nonquasisimple_canonical_residual_structure
      (sylowNormalizedMaximalLocalUniqueNormalizer_of h37 h38 h39) hA7n hnab hQ hT hLmax hLf hTL
      hLq
  have hC := hall p hp hp5 hCp
  have hS : SCSetup T L (nqPrimeResidualX L p) p :=
    ⟨hs, hnab, hQ, hT, hLmax, hLf, hTL, hLq, hp, hp5, hA, hC⟩
  exact ⟨L, nqPrimeResidualX L p, ⟨hLmax, hLf⟩, hLq, hTL, hC.le_rad,
    unique_maximal_overgroup_of hO hN hP hS, h5 G T L hs hnab hQ hT hLf hTL hLq⟩

end CFSG.Quasithin.H13.NQCore

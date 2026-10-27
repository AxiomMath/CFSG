module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate120
import CFSG.LocalAnalysis.StandardType.GGStdPosAutHolds
import CFSG.LocalAnalysis.StandardType.GGStdPosLeviHolds
import CFSG.LocalAnalysis.StandardType.GGStdPosCardHolds
import CFSG.LocalAnalysis.StandardType.GGSecFivePresTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggKGPos_tableBPos_of_stdPos :
    GGKGPosStep fun (G : Type) [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G)
      (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G) => GGTableBPos p Bs X t n f ψ := by
  intro G _ _ p Bs X t n f ψ hloc hstd
  obtain ⟨ν, hν⟩ := (ggTagFacts_of_admissible hloc.1.2.2.1 hloc.1.2.2.2).2.1
  obtain ⟨ε, hε⟩ := ggKGPosAutWeylStmt_holds G p Bs X t n f ψ hloc hstd ν hν
  exact ⟨ε, ggKGPosReflStmt_holds G p Bs X t n f ψ hloc hstd ν ε hν hε,
    ggKGPosLeviStmt_holds G p Bs X t n f ψ hloc hstd ν ε hν hε,
    ggKGPosCardStmt_holds G p Bs X t n f ψ hloc hstd⟩

end CFSG.StandardType

end

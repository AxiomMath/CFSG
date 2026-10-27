module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosRankDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGStdPosTableBPos
import CFSG.LocalAnalysis.StandardType.GGStdPosRankBase
import CFSG.LocalAnalysis.StandardType.GGStdPosRankHolds
import CFSG.LocalAnalysis.StandardType.GGStdPosLocalConj
import CFSG.LocalAnalysis.StandardType.GGStdPosA
import CFSG.LocalAnalysis.StandardType.GGStdPosD
import CFSG.LocalAnalysis.StandardType.GGStdPosE6
import CFSG.LocalAnalysis.StandardType.GGStdPosE6Three
import CFSG.LocalAnalysis.StandardType.GGStdPosE7
import CFSG.LocalAnalysis.StandardType.GGStdPosE8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggKGPosRankStmt_holds :
    GGKGPosRankStmt := by
  intro G _ _ p B Bs x L D J 𝒦 h X hX hsplit
  obtain ⟨t, n, f, ψ, hbase⟩ := ggKGPosBaseStmt_holds G p B Bs x L D J 𝒦 h X hX hsplit
  exact ⟨t, n, f, ψ, ggKGPosLocalHyp_iff.mpr
    ⟨hbase, ggKGPosBoundsStmt_holds G p B Bs x L D J 𝒦 h X hX hsplit t n f ψ hbase⟩⟩

theorem ggKGPos_exists_stdPos
    {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (h : GGKGPosLocalHyp p Bs X t n f ψ) :
    ∃ k : (ggU t n f).K, GGKGPosStdPos (ggU t n f).D (ψ.comp (MulAut.conj k).toMonoidHom) Bs := by
  rcases h.2.1.2.2.1 with rfl | rfl | rfl | rfl | rfl
  · by_cases hpn : p ∣ n
    · exact ggKGPosStdPosATors G p Bs X n f ψ h hpn
    · exact ggKGPosStdPosA G p Bs X n f ψ h hpn
  · exact ggKGPosStdPosD G p Bs X n f ψ h trivial
  · by_cases hp3 : p = 3
    · exact ggKGPosStdPosE6Three G p Bs X n f ψ h hp3
    · exact ggKGPosStdPosE6 G p Bs X n f ψ h hp3
  · exact ggKGPosStdPosE7 G p Bs X n f ψ h trivial
  · exact ggKGPosStdPosE8 G p Bs X n f ψ h trivial

theorem ggSecFiveKGPosInput_holds :
    GGSecFiveKGPosInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _ _ _ _ _ _ X hX hsplit
  obtain ⟨t, n, f, ψ, hloc⟩ := ggKGPosRankStmt_holds G p B Bs x L D J 𝒦 hcfg X hX hsplit
  obtain ⟨k, hstd⟩ := ggKGPos_exists_stdPos hloc
  have hloc' := ggKGPosLocalHyp_comp_conj hloc k
  exact ⟨t, n, f, ψ.comp (MulAut.conj k).toMonoidHom, hloc'.1.2.2.1, hloc'.1.2.2.2, hloc'.2.1.1,
    hloc'.2.1.2.1, hloc'.2.1.2.2.1, hloc'.2.1.2.2.2,
    ggKGPos_tableBPos_of_stdPos G p Bs X t n f _ hloc' hstd⟩

end CFSG.StandardType

end

module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFGF2
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLStdJ
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLA5
public import CFSG.RankThree.PartTwo.Sec21.HeringFFSHolds
public import CFSG.RankThree.PartTwo.Sec21.LitScopeProof
import CFSG.RankThree.PartTwo.Sec21.Item233TablesMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.GF2n

section CertifiedFF

theorem item212XL45_of_papers_gf2 (hGF2 : GF2TypeStatementKP) (hb : Item310Bridges)
    (h79 : FF79Extraspecial) (h81 : FF81TheoremAK) (h84 : FF84Extraspecial) : Item212XL45 := by
  intro G _ _ A E U c L hpair hA27 φ hφ X hX hK a haA ha1 hXa _ hθ hL
  by_contra hW
  have hpt : Sec21Point G A a X :=
    { hpair.toSec21Std with mem := haA, ne_one := ha1, mem_lStar := hX, mem_theta := hXa }
  have eX : X ≃* lBar X := mulEquiv_lBar_of_theta_eq_bot hθ
  have hXmod : IsL4L5Sp6 X := by
    rcases hL with hL | hL
    · exact Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv eX.symm hL)
    · exact Or.inr (Or.inl (CFSG.SectionRank.statedClassicalModel_of_mulEquiv eX.symm hL))
  have hQ : CFSG.IsQuasisimple (lBar X) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hXa
  haveI := ff_isSimpleGroup_lBar hXmod
  have hXs : IsSimpleGroup X := eX.isSimpleGroup
  obtain ⟨p, q, hpq⟩ := ff_exists_noncomm_of_isQuasisimple hQ
  have hXq : CFSG.IsQuasisimple X := Tables.isQuasisimple_of_isSimpleGroup hXs
    ⟨eX.symm p, eX.symm q, fun h => hpq (by simpa using congrArg eX h)⟩
  exact ff_false_papers_gf2 hGF2 hb h79 h81 h84 (ffCentCyclic_of_kE9 fFKE9_holds)
    (ffLocalRankC_of_kE9 fFKE9_holds) ffSylowIsAL45_holds ffPRankL5_holds
    (ffStandardJL5_of_cyc (ffCentCyclic_of_kE9 fFKE9_holds)) ffHypA5Sp6_holds ffCenterSp6_holds
    hpt hXq hXmod (ffCentralizerNormalizes_of_kE9 fFKE9_holds G A a X hpt hXmod hXq) hW

end CertifiedFF

end CFSG.RankThree.PartTwo.Sec21

module

public import Certificates.Certificate111602
public import CFSG.RankThree.PartTwo.J2Residue.H2Sylow

public section

namespace CFSG.RankThree.PartTwo.J2Residue.H2

open CFSG.ComponentClassification.J2Cover.Models

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {ρ : ↥P →* Module.End (ZMod 2) V12}

theorem exists_cob_of_isNormCoc (hρ : IsMRep ρ)
    {c : ↥P → ↥P → V12} (hc : IsNormCoc ρ c) : ∃ β : ↥P → V12, c = cob ρ β :=
  Certificates.certificate111602 ρ hρ c hc

end CFSG.RankThree.PartTwo.J2Residue.H2

module

public import CFSG.RankThree.GF2n.DecompSetupNat
public import Certificates.Certificate113
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate43
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

open scoped IsMulCommutative

namespace CFSG.RankThree.GF2n

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.GH74.Uniqueness.Bender Matrix
open CFSG.Timmesfeld CFSG.Timmesfeld.ARS CFSG.Timmesfeld.RankOne
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace DecompSetup

variable {A Ab L Lb M : Subgroup G} (S : DecompSetup A Ab L Lb M)
include S

section Quot

variable [(M.subgroupOf (A ⊔ Ab)).Normal]

local notation "πm" => QuotientGroup.mk' (Subgroup.subgroupOf M (A ⊔ Ab))

variable (P : QuotPair ((A.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab))))
  ((Ab.subgroupOf (A ⊔ Ab)).map (QuotientGroup.mk' (M.subgroupOf (A ⊔ Ab)))))
include P

end Quot

end DecompSetup

end CFSG.RankThree.GF2n

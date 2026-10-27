module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporMK
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporMThompson
public import Certificates.Certificate812201

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.MK

open Subgroup CFSG.Monster.Existence

theorem k105SporAt_M_of_certificates :
    K105SporAt .M :=
  k105SporAt_M_of_thompsonJ
    (exists_isSylowTwoOf_k105In_thompsonJ_Gmat Certificates.certificate812201
      CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder fun _ hT hTz =>
        k105In_centralizer_of_isTwoBCentralizer
          (isTwoBCentralizer_Gmat xGmat (IsConj.refl _)) hT hTz)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.MK

module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporAt
public import CFSG.Quasithin.H13.NQCatT513J4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.QuasithinUnique
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Rad
  CFSG.Quasithin.A312M24 CFSG.Quasithin.J4Fam

theorem k105SporAt_J4 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] :
    K105SporAt .J4 := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .J4 ≃* ↥J := seedEquiv j4Facts.mat
  exact k105SporAt_of_index (s := .J4) isSylowTwoOf_P0
    (fun _ hPZ hZs _ hm => CFSG.Quasithin.H13.NQCat.T513P.index_of_solvable_J hPZ hZs hm) e

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10

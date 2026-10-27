module

public import CFSG.Milestones.ASVolI.A3Spor.Core
public import CFSG.Quasithin.H13.NQCatT513J4

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Rad
  CFSG.Quasithin.A312M24 CFSG.Quasithin.J4Fam

theorem burnsideA315s_noConfig_J4Grp :
    ∀ S B : Subgroup ↥J, ¬ burnsideA315x_Config ↥J S B := fun _ _ hc =>
  burnsideA315s_false_of_overgroups isSylowTwoOf_P0
    (fun _ hPZ hZs _ hm => CFSG.Quasithin.H13.NQCat.T513P.index_of_solvable_J hPZ hZs hm) hc

theorem burnsideA315s_noConfig_J4 :
    ∀ S B : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .J4),
      ¬ burnsideA315x_Config (CFSG.Blueprint.NativeSporadic.Carrier .J4) S B := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .J4 ≃* ↥J := seedEquiv j4Facts.mat
  exact @burnsideA315s_noConfig_of_equiv (CFSG.Blueprint.NativeSporadic.Carrier .J4) ↥J _ _ e
    burnsideA315s_noConfig_J4Grp

end CFSG.ASVolI

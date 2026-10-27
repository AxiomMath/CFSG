module

public import CFSG.Certificates.Kernel.DELKSound
public import Certificates.Kernel.DELK.C
public import Certificates.Kernel.DELK.V
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.DELK

open Certificates.DELK

#kc_forall_tree allG (fun i => kBaseAt P S i = true) 2 CFSG.KD.DELK.ch709539g

#kc_forall_tree allC (fun i => kConjAt P S C i = true) 2 CFSG.KD.DELK.ch709539c

#kc_forall_tree allO (fun i => kPat1At H Z P O i = true) 3 CFSG.KD.DELK.ch709539o

#kc_forall_tree allT (fun i => kPat2At H Z P T i = true) 6 CFSG.KD.DELK.ch709539t

theorem twoPZ : T.all (fun e => e.2.2.all fun c => c.2.1 == 2) = true := by decide +kernel

theorem cells : CFSG.StandardType.GGDepED4LowCells :=
  CFSG.StandardType.DELK.delk_sound H Z P O T S C pairsOK conjShapes
    (fun i hi => allG i (by rwa [lenS] at hi)) (fun i hi => allC i (by rwa [lenC] at hi))
    groupsCover cover (fun i hi => allO i (by rwa [lenO] at hi))
    (fun i hi => allT i (by rwa [lenT] at hi)) twoPZ

end CFSG.KD.DELK

end

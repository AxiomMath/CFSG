module

public import CFSG.Quasithin.AppendixH.H14.H141Table
public import CFSG.Quasithin.AppendixH.H14.H141Lin
public import CFSG.Quasithin.AppendixH.H14.H141Tabs
public import CFSG.Quasithin.AppendixH.H14.H141TData
public import CFSG.Quasithin.AppendixH.H14.H141T1Data

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.ASVolI.ChH

theorem tabT_ok : tab64OK tabT = true := by decide +kernel

theorem gensT_stab : gensT.all (fun a =>
    inAutOK a && trioMasks.all fun m => trioMasks.contains (permM a m)) = true := by
  decide +kernel

theorem tabT_stab : (List.range 64).all (fun n =>
    trioMasks.all fun m => trioMasks.contains (permM tabT[n]! m)) = true := by
  decide +kernel

theorem cmapT_gens : (List.range 2).all (fun j => (List.range 64).all fun n =>
    cmap64 tabT gensT[j]! n == linAct (gmT.getD j 0) n) = true := by
  decide +kernel

theorem bfsT_ok : sbfsOK gmT bfsT = true := by decide +kernel

theorem bfsT_length : bfsT.length = 1008 := by decide +kernel

theorem vbT1_ok : vbfs64OK tabT gensT 1 vbT1 = true := by decide +kernel

theorem vbT2_ok : vbfs64OK tabT gensT 10 vbT2 = true := by decide +kernel

theorem vbT_cover : (List.range 64).all (fun n =>
    n == 0 || (vbT1.map Prod.fst).contains n || (vbT2.map Prod.fst).contains n) = true := by
  decide +kernel

theorem derT1_ok : derivOK (vbT1.map Prod.fst) derT1 = true := by decide +kernel

theorem vbT_link : (vbT2.map Prod.fst).any (fun b =>
    (vbT2.map Prod.fst).any fun b' => (vbT1.map Prod.fst).contains (b ^^^ b')) = true := by
  decide +kernel

end CFSG.Quasithin.AppendixH.H14

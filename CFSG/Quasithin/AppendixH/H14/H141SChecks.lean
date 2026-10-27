module

public import CFSG.Quasithin.AppendixH.H14.H141Table
public import CFSG.Quasithin.AppendixH.H14.H141Lin
public import CFSG.Quasithin.AppendixH.H14.H141Tabs
public import CFSG.Quasithin.AppendixH.H14.H141SData
public import CFSG.Quasithin.AppendixH.H14.H142StdDefs

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.ASVolI.ChH

theorem tabS_ok : tab64OK tabS = true := by decide +kernel

theorem gensS_stab : gensS.all (fun a =>
    inAutOK a && stdMasks.all fun m => stdMasks.contains (permM a m)) = true := by
  decide +kernel

theorem tabS_stab : (List.range 64).all (fun n =>
    stdMasks.all fun m => stdMasks.contains (permM tabS[n]! m)) = true := by
  decide +kernel

theorem cmapS_gens : (List.range 2).all (fun j => (List.range 64).all fun n =>
    cmap64 tabS gensS[j]! n == linAct (gmS.getD j 0) n) = true := by
  decide +kernel

theorem bfsS_ok : sbfsOK gmS bfsS = true := by decide +kernel

theorem bfsS_length : bfsS.length = 2160 := by decide +kernel

theorem vbS1_ok : vbfs64OK tabS gensS 1 vbS1 = true := by decide +kernel

theorem vbS2_ok : vbfs64OK tabS gensS 5 vbS2 = true := by decide +kernel

theorem vbS_cover : (List.range 64).all (fun n =>
    n == 0 || (vbS1.map Prod.fst).contains n || (vbS2.map Prod.fst).contains n) = true := by
  decide +kernel

theorem derS1_ok : derivOK (vbS1.map Prod.fst) derS1 = true := by decide +kernel

theorem vbS_link : (vbS2.map Prod.fst).any (fun b =>
    (vbS2.map Prod.fst).any fun b' => (vbS1.map Prod.fst).contains (b ^^^ b')) = true := by
  decide +kernel

end CFSG.Quasithin.AppendixH.H14

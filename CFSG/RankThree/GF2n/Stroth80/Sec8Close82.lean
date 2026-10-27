module

public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsAssembly
public import CFSG.RankThree.GF2n.Stroth80.Sec8HMain
public import CFSG.RankThree.GF2n.Stroth80.Sec84StrongClosure
public import CFSG.RankThree.GF2n.Stroth80.Sec8V1InterDim
public import CFSG.RankThree.GF2n.Stroth80.Sec8OuterTight
public import CFSG.RankThree.GF2n.Stroth80.Sec8BridgeData
public import CFSG.RankThree.GF2n.Stroth80.Sec8OuterInter
public import CFSG.RankThree.GF2n.Stroth80.Sec8OuterLB
public import CFSG.RankThree.GF2n.Stroth80.Sec8DimCount
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsDPrime

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


theorem close82False_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (h53 : Stroth53Statement) (h310chi : Stroth310ChiStatement)
    (hA : Sec8AExistsStatement) (hzt : Sec8ZtStatement) : Close82FalseStatement := by
  intro G _ _ M Q Z B hc n t r hC
  obtain ⟨g, hg⟩ := sec8Outer_of_close82 hC
  have hs := hg.hs
  have hs5 := hs.toSec5
  have hm2 : SpMNat hc t 2 := hC.2.2.2.1
  have hD' := sec8DPrime_of h51 hA sec8PointsTrans_holds sec8PointTI_of
  have hS : Sec8StrongClosureStatement :=
    sec8StrongClosure_of h51 hA hzt h310chi h53 stroth56Sp_holds
      (sec8V1InterDim_of h51 hA hzt h310chi h53.1) (sec8LemmaH_of h34 hRoot h51 h53 h310chi)
  have hZV := sec8ZV_of_inputs h51 hA hzt h310chi
  obtain ⟨-, htightW, htightV⟩ := sec8_outer_tight h34 hRoot h53 h310chi hg hm2
  have hinter := sec8_outer_inter hD' h53 hg
  have hnorm := sec8_outer_normLB hg
  obtain ⟨l, hl, hlx⟩ := sec8_outer_exists_l h34 hg hinter
  have hclaim := sec8_outer_claimB hD' hS hZV hg hinter hl hlx hnorm
  have hV : Vt M (LB M Q B) B Z t = Ut Q Z t :=
    (h310chi G M Q Z B hc n t hs5 (Or.inl hs.spNat)).1
  have h53b := (h53.2.1 G M Q Z B hc n t hs5 hs.spNat r hg.hr.mem hg.hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r)
    rfl rfl rfl rfl rfl).2
  have hcard := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.2.2
  obtain ⟨K, iF, iFin, iCh, E, iE, iM, iMF, B', X, X', L, S, Bpt, hnd, halt, hXiso, hX'iso, hXs,
    hX's, haa, hE'', hdisj, hL, hdim, hSiso, hScard, hBcard, hSe, hSL⟩ :=
    sec8_bridge_data hc hg hl hm2 hV h53b hnorm htightW htightV hclaim hs5.width hcard
  exact sec8_dimCount_of_K B' hnd halt X X' L hXiso hX'iso hXs hX's haa hE'' hdisj hL hdim S Bpt
    hSiso hScard hBcard hSe hSL

end

end CFSG.RankThree.GF2n.Stroth80

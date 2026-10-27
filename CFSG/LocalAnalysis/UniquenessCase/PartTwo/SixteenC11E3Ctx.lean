module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3OutAll
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11R1610Two
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.W3Lem45Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBMain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

structure S1611e3Std (D : Data G) : Prop where
  hx : DataExt D
  he : evenRank G = 3
  hSg : UC6S846.SigmaStd D
  h61 : UC6.R6_1 D
  h127 : R127 D
  h1114 : R1114 D
  h126 : R126 D
  h1214 : F12.R1214 D
  h111 : W3Thm111 G
  h162 : W3Thm162Ext G
  h139 : Hyp139
  h1211 : R1211_1 D
  h1217 : R1217 D
  h153 : R15_3Small D
  h119 : F11.R119 D
  h78 : R7_8At3 D
  h96 : UC9R96.R9_6At7 D
  h921 : R9_21Opp D
  h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1

theorem S1611e3Std.r16_9 {D : Data G} (h : S1611e3Std D) {V₀ V : Subgroup G}
    (h125 : Hyp125 D V₀ V) : R16_9 D :=
  r16_9_holds D h.hSg (h.h1219 V₀ V h125) h.hx h.h61 h.h127 h.h1217

theorem S1611e3Std.in10 {D : Data G} (h : S1611e3Std D) {V₀ V : Subgroup G}
    (h125 : Hyp125 D V₀ V) : In10 D :=
  ⟨h.hSg, h.h1219 V₀ V h125, h.hx, h.h61, h.h127, h.h1114, h.h126, h.h1214, h.h162, h.h139,
    h.r16_9 h125⟩

section Certified


theorem S1611e3Std.out10 {D : Data G} (h : S1611e3Std D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) : Out10 D V₀ V hV :=
  s16t_out10_of_concl168_three D (h.in10 hc.setting.hyp16.hyp125) h.h1217 h.h153 h.h119 h.h78
    h.h96 h.h921 hc

theorem S1611e3Std.r16_10_2 {D : Data G} (h : S1611e3Std D) {V₀ V : Subgroup G}
    (h125 : Hyp125 D V₀ V) : R16_10_2 D :=
  r16_10_2_of_out10 D h.hSg (h.h1219 V₀ V h125) h.hx h.h61 h.h127 h.h1114 (w3Lem45_2_holds G)
    (fun _ _ _ _ hc => h.out10 hc)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

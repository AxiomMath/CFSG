module

public import CFSG.Quasithin.H13.GoldschmidtC137CFrame
public import CFSG.Quasithin.H13.GoldschmidtC137Tail

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

structure C137Base [Finite G] (X T V L P : Subgroup G) : Prop where
  hT : IsSylowTwoOf T X
  hTP : T ≤ P
  hPX : P < X
  hred : IsTwoReducedIn X V
  hVe : IsElemAbelian 2 V
  hLX : L ≤ X
  hXN : X ≤ normalizer (V : Set G)
  hRT : pCoreOf 2 P ≤ T
  hQT : pCoreOf 2 X ≤ T
  hTCR : T ⊓ centralizer (V : Set G) ≤ pCoreOf 2 P
  toBaum : BaumCtx X T V L P

abbrev C137FrameB [Finite G] {X T V L P : Subgroup G} (h : C137Base X T V L P) :=
  C137Frame h.hVe X T L

end CFSG.Quasithin.H13.U3.GC137

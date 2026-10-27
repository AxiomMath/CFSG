module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalDich
public import CFSG.Quasithin.Recognition.Kleidman.F204.CritBasic

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Quasithin CFSG.Quasithin.FA5 CFSG.Quasithin.F53

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem frame_dichotomy (F : Frame L1 L2 S D X) (δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)) :
    ZCentral δ ∨ ZFaithful δ := dichotomy F δ

end CFSG.Quasithin.Kleidman.F204

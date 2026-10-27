module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def LemmaD (F : FanTree Γ G) : Prop :=
  Fan40 F → ∀ l d : V, l ≠ d → valence Γ l = 5 → valence Γ d = 5 →
    (Γ.dist l d = 2 ∨ Γ.dist l d = 4) → ∀ w : G, w ∈ Cinv G l → w ∈ Cinv G d → False

end CFSG.Quasithin.Fan86

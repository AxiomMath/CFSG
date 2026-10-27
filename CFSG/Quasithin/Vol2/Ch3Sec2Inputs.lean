module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13

@[expose] def AsI16Cover328 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → ∀ L : Subgroup (MulAut V),
    commV L ∈ IrrPlus L ⊤ →
      ((AlternatingNatural L (commV L) (fixV L ⊓ commV L) 5 ∨
          AlternatingNatural L (commV L) (fixV L ⊓ commV L) 7 ∨
          (∃ n, 1 < n ∧ BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 n) ∨
          BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 4 1 ∨
          BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 5 1 ∨
          SLExteriorTwo L (commV L) (fixV L ⊓ commV L) 5 ∨
          A7Four L (commV L) (fixV L ⊓ commV L) ∨
          TripleA6Six L (commV L) (fixV L ⊓ commV L)) →
        fixV L ⊓ commV L = ⊥) ∧
      (BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 1 →
        Nat.card ↥(fixV L ⊓ commV L) ≤ 2)

end CFSG.Quasithin.H13

module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrack

public section

namespace CFSG.Quasithin.Stroth.Rq

@[expose] def Str83RqO4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a f : ℕ),
    Frame L1 L2 S a f → f ≠ 2 * a + 1 → ∀ t : Track L1 L2 S, t.GT = t.K

end CFSG.Quasithin.Stroth.Rq

end

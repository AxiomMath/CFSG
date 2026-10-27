module

public import CFSG.Quasithin.EmptyFaithful.F112HypW
public import CFSG.Quasithin.Recognition.Stroth.SliceSzUReduction

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F112R

@[expose] def IdSzL2W : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (a : ℕ),
    F112HypW L1 L2 S → 1 ≤ a → Nonempty (oTwoQuot ↥L1 ≃* Sz a) → VBig L2 → VL2 L2 →
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) ∧
        IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsTwistedF4Over (2 * a + 1))

theorem IdSzL2W.idSzL2 (h : IdSzL2W) : IdSzL2 :=
  fun G _ _ L1 L2 S a hF => h G L1 L2 S a hF.toW

end CFSG.Quasithin.Stroth

end

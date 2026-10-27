module

public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3

public section

namespace CFSG.Quasithin.ASInputs

@[expose] def AS_I_1_6_cover : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Gm : Subgroup (MulAut W)) (d : ℕ),
      commV Gm = ⊤ → I16Module Gm ⊤ (fixV Gm) d → Nat.card (fixV Gm) ≤ 2 ^ d

@[expose] def AS_I_1_6_dual : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Gm : Subgroup (MulAut W)) (d : ℕ),
      fixV Gm = ⊥ → I16Module Gm (commV Gm) ⊥ d → (commV Gm).index ≤ 2 ^ d

theorem lemI1_6_of (ha : AS_I_1_6_cover) (hb : AS_I_1_6_dual) : AS_I_1_6 :=
  fun W _ _ hW Gm d => ⟨ha W hW Gm d, hb W hW Gm d⟩

end CFSG.Quasithin.ASInputs

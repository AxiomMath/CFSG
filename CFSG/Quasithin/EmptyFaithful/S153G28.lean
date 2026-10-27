module

public import CFSG.Quasithin.EmptyFaithful.S153G27
public import CFSG.Quasithin.EmptyFaithful.S153D28

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

@[expose] def Input28A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15328 T Mc M V₁ V₂ Yp I L t → ¬ IsAlt 7 ↥(Star153 T I L)

@[expose] def Input28Insp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15328 T Mc M V₁ V₂ Yp I L t → B56QuasisimpleList ↥(Star153 T I L) →
      ¬ IsAlt 7 ↥(Star153 T I L) → Concl15328 T M V₁ I L

theorem input15328_of_narrow (hL : Input27List) (h7 : Input28A7) (hi : Input28Insp) :
    Input15328 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c
  have hlist := hL G T Mc M V₁ V₂ Yp I L t c.toCtx15327.toCtx15325L
  exact hi G T Mc M V₁ V₂ Yp I L t c hlist (h7 G T Mc M V₁ V₂ Yp I L t c)

end CFSG.Quasithin

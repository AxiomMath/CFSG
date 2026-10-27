module

public import CFSG.Quasithin.EmptyFaithful.T1531InspBasic
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.F6Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Gold2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def IsInspList (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* ↥(StatedSL 3 (ZMod 2))) ∨ IsAlt 6 X ∨ Nonempty (X ≃* Equiv.Perm (Fin 6)) ∨
    IsAlt 7 X ∨ Nonempty (X ≃* Equiv.Perm (Fin 7)) ∨ F6.IsHatAlt 6 X ∨
    Nonempty (X ≃* ↥(CFSG.Open.quasithinG2 (ZMod 2))) ∨
    Nonempty (X ≃* ↥⁅CFSG.Open.quasithinG2 (ZMod 2), CFSG.Open.quasithinG2 (ZMod 2)⁆)

@[expose] def InspectListF618 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (D₁ D₂ J N : Subgroup D),
    IsGoldschmidtAmalgam D₁ D₂ → F6.F618ConclusionCat D₁ D₂ →
    J ≤ D₁ → IsPGroup 2 ↥J → D₁ ≤ Subgroup.normalizer (J : Set D) →
    ⁅oTwoUpper D₂, J⁆ = oTwoUpper D₂ → N = Subgroup.normalClosure (J : Set D) →
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ ρ : D →* MulAut W, Function.Injective ρ → B53Hyp (N.map ρ) →
        (B56Case1 (N.map ρ) ∨ B56Case2 (N.map ρ) ∨ B56Case3 (N.map ρ) ∨ B56Case4 (N.map ρ) ∨
          B56Case5 (N.map ρ)) →
        Nonempty (↥N ≃* Equiv.Perm (Fin 3)) ∨ (IsInspList ↥N ∧ oTwoUpper (⊤ : Subgroup D) ≤ N)

abbrev Xdot153 {G : Type} [Group G] (T Mc M E : Subgroup G) (s : G) :
    Subgroup (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) :=
  barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
    (thompsonJ (G0_153 T Mc M E s))

@[expose] def InspectRemaining153 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
    LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E → Res15367 T Mc M V₁ V₂ E →
    GoldLine153 T V₁ E s → Res15368 T Mc M E s →
    F6.F618ConclusionCat
      (((G1_153 T Mc M E s).subgroupOf (G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))))
      (((G2_153 T E).subgroupOf (G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))) →
    IsInspList ↥(Xdot153 T Mc M E s) →
    ¬ Nonempty (↥(Xdot153 T Mc M E s) ≃* Equiv.Perm (Fin 3)) →
    oTwoUpper (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) ≤
      Xdot153 T Mc M E s →
    ¬ Group.IsSolvable ↥(thompsonJ (G0_153 T Mc M E s) ⊓ Subgroup.normalizer (V₁ : Set G))

end CFSG.Quasithin

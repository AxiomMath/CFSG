module

public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.EmptyFaithful.T1531InspMod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

structure Conf153 (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G) :
    Prop where
  ctx : Ctx153 G T Mc M V₁ V₂ t
  r45 : Res15345 T Mc M V₁ V₂
  r46 : Res15346 T M V₁ V₂
  r49 : Res15349 T Mc M V₁
  line : LineData153 T M V₁ V₂ E
  r66 : Res15366B T Mc M V₁ V₂ E
  r67 : Res15367 T Mc M V₁ V₂ E
  gl : GoldLine153 T V₁ E s
  r68 : Res15368 T Mc M E s

@[expose] def InspectB51Rem153 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Conf153 G T Mc M V₁ V₂ E t s →
    F6.F618ConclusionCat
      (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G1_153 T Mc M E s))
      (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G2_153 T E)) →
    IsInspList ↥(Xdot153 T Mc M E s) →
    ¬ Nonempty (↥(Xdot153 T Mc M E s) ≃* Equiv.Perm (Fin 3)) →
    oTwoUpper (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) ≤
      Xdot153 T Mc M E s →
    oTwoUpper (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) ≠
      ⊤ →
    YF153 Mc M E s ≤ thompsonJ (G0_153 T Mc M E s) ⊔ pCoreOf 2 (G0_153 T Mc M E s) →
    pCoreOf 2 (YF153 Mc M E s) ⊔ pCoreOf 2 (G0_153 T Mc M E s) ≤
      Subgroup.centralizer (VZ T M : Set G) →
    ⁅VZ T M, YF153 Mc M E s⁆ = VZ T M →
    G1_153 T Mc M E s ≤ Subgroup.normalizer (VZ T M : Set G) →
    ¬ pCoreOf 2 (G1_153 T Mc M E s) ≤ Subgroup.centralizer (VZ T M : Set G) →
    F6.IsHatSym 6 (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) ∧
      Nat.card ↥(V0_153 T Mc M E s) = 2 ^ 6

@[expose] def InspectA5Quot153 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Conf153 G T Mc M V₁ V₂ E t s →
    F6.F618ConclusionCat
      (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G1_153 T Mc M E s))
      (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G2_153 T E)) →
    IsInspList ↥(Xdot153 T Mc M E s) →
    ¬ Nonempty (↥(Xdot153 T Mc M E s) ≃* Equiv.Perm (Fin 3)) →
    oTwoUpper (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) ≤
      Xdot153 T Mc M E s →
    YF153 Mc M E s ≤ thompsonJ (G0_153 T Mc M E s) ⊔ pCoreOf 2 (G0_153 T Mc M E s) →
    pCoreOf 2 (YF153 Mc M E s) ⊔ pCoreOf 2 (G0_153 T Mc M E s) ≤
      Subgroup.centralizer (VZ T M : Set G) →
    ⁅VZ T M, YF153 Mc M E s⁆ = VZ T M →
    F6.IsHatSym 6 (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) →
    Nat.card ↥(V0_153 T Mc M E s) = 2 ^ 6 →
    ¬ Group.IsSolvable ↥(thompsonJ (G0_153 T Mc M E s) ⊓ Subgroup.normalizer (V₁ : Set G))

end CFSG.Quasithin

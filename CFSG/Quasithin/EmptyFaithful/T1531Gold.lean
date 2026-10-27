module

public import CFSG.Quasithin.Background.F6Solvable
public import CFSG.Quasithin.EmptyFaithful.T1531Stage3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Vocabulary

variable {G : Type} [Group G]

structure LineData153 (T M V₁ V₂ E : Subgroup G) : Prop where
  le_V : E ≤ VZ T M
  card_eq : Nat.card E = 4
  totSingular : IsTotSingular153 T M V₁ V₂ E
  not_le_M : ¬ Subgroup.normalizer (E : Set G) ≤ M
  sylow : IsSylowTwoOf (T ⊓ Subgroup.normalizer (E : Set G)) (M ⊓ Subgroup.normalizer (E : Set G))

abbrev TE153 (T E : Subgroup G) : Subgroup G := T ⊓ Subgroup.normalizer (E : Set G)

abbrev YE153 (Mc M E : Subgroup G) : Subgroup G :=
  oTwoUpper (Y153 Mc M ⊓ Subgroup.normalizer (E : Set G))

abbrev QE153 (E : Subgroup G) : Subgroup G := pCoreOf 2 (Subgroup.normalizer (E : Set G))

abbrev XE153 (E : Subgroup G) : Subgroup G := oTwoUpper (Subgroup.centralizer (E : Set G))

noncomputable abbrev Omega4Plus153 (T M V₁ V₂ : Subgroup G) : Subgroup (MulAut ↥(VZ T M)) :=
  autOn (M ⊓ Subgroup.centralizer (V₂ : Set G)) (VZ T M) ⊔
    autOn (M ⊓ Subgroup.centralizer (V₁ : Set G)) (VZ T M)

@[expose] def IsKleinFour153 {X : Type*} [Group X] (A : Subgroup X) : Prop :=
  Nat.card A = 4 ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a ^ 2 = 1

structure GoldLine153 (T V₁ E : Subgroup G) (s : G) : Prop where
  s_mem : s ∈ Sgp153 T V₁
  s_not_mem : s ∉ TE153 T E

abbrev FE153 (E : Subgroup G) (s : G) : Subgroup G := conjSubgroup E s

abbrev YF153 (Mc M E : Subgroup G) (s : G) : Subgroup G := conjSubgroup (YE153 Mc M E) s

abbrev G1_153 (T Mc M E : Subgroup G) (s : G) : Subgroup G := YF153 Mc M E s ⊔ TE153 T E

abbrev G2_153 (T E : Subgroup G) : Subgroup G := XE153 E ⊔ TE153 T E

abbrev G0_153 (T Mc M E : Subgroup G) (s : G) : Subgroup G :=
  G1_153 T Mc M E s ⊔ G2_153 T E

end Vocabulary

structure Res15366 {G : Type} [Group G] (T Mc M V₁ V₂ E : Subgroup G) : Prop where
  barTE_eq : autOn (TE153 T E) (VZ T M) = autOn T (VZ T M) ⊓ Omega4Plus153 T M V₁ V₂
  relIndex_two : (TE153 T E).relIndex T = 2
  barTE_klein : IsKleinFour153 (autOn (TE153 T E) (VZ T M)) ∧
    autOn (TE153 T E) (VZ T M) ≠ autOn (Sgp153 T V₁) (VZ T M)
  Z_le_E : quasithinOmegaOneCenter T ≤ E
  quot_S3 : Nonempty (OTwoQuot (YE153 Mc M E ⊔ TE153 T E) ≃* Equiv.Perm (Fin 3))
  V_comm : ⁅VZ T M, YE153 Mc M E⁆ = VZ T M
  QE_le : QE153 E ≤ Subgroup.centralizer (E : Set G)
  pCore_YETE : pCoreOf 2 (YE153 Mc M E ⊔ TE153 T E) =
    (YE153 Mc M E ⊔ TE153 T E) ⊓ Subgroup.centralizer (E : Set G)
  induces_GL : autOn (YE153 Mc M E ⊔ TE153 T E) E = ⊤
  GE_eq : Subgroup.normalizer (E : Set G) =
    (YE153 Mc M E ⊔ TE153 T E) ⊔ Subgroup.centralizer (E : Set G)
  centralizer_le_mc : Subgroup.centralizer (E : Set G) ≤ Mc

@[expose] def Stage15366 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ →
      LineData153 T M V₁ V₂ E → Res15366 T Mc M V₁ V₂ E

structure Res15367 {G : Type} [Group G] (T Mc M V₁ V₂ E : Subgroup G) : Prop where
  R_eq : T ⊓ Subgroup.centralizer (VZ T M : Set G) = Subgroup.centralizer (VZ T M : Set G)
  M_eq : M = Y153 Mc M ⊔ T
  sylow_GE : IsSylowTwoOf (TE153 T E) (Subgroup.normalizer (E : Set G))
  baum_le : baum (TE153 T E) ≤ T ⊓ Subgroup.centralizer (VZ T M : Set G)
  CGS_le : CGS (baum (TE153 T E)) ≤ M
  GE_eq : Subgroup.normalizer (E : Set G) = (YE153 Mc M E ⊔ XE153 E) ⊔ TE153 T E
  XE_not_le : ¬ XE153 E ≤ M
  XE_quot : Nonempty (OTwoQuot (XE153 E) ≃* Multiplicative (ZMod 3))
  YE_quot : Nonempty (OTwoQuot (YE153 Mc M E) ≃* Multiplicative (ZMod 3))
  YE_normal : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (YE153 Mc M E : Set G)
  XE_normal : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (XE153 E : Set G)
  quot_S3S3 : Nonempty (OTwoQuot (Subgroup.normalizer (E : Set G)) ≃*
    Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  XE_comm : XE153 E = ⁅XE153 E, thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G))⁆

@[expose] def Stage15367 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
      Res15350 T M → LineData153 T M V₁ V₂ E → Res15366 T Mc M V₁ V₂ E → Res15367 T Mc M V₁ V₂ E

structure Res15368 {G : Type} [Group G] (T Mc M E : Subgroup G) (s : G) : Prop where
  le_normalizer : G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G)
  V_le_pCore : VZ T M ≤ pCoreOf 2 (G0_153 T Mc M E s)
  pCore_le_centralizer : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (VZ T M : Set G)
  sylow_of_inM : ∀ M₀ : Subgroup G, InM (G0_153 T Mc M E s) M₀ → IsSylowTwoOf (TE153 T E) M₀
  triple : F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E)
  pCore_eq : pCoreOf 2 (G0_153 T Mc M E s) =
    (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map (G0_153 T Mc M E s).subtype

@[expose] def Stage15368 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
      Res15350 T M → LineData153 T M V₁ V₂ E → Res15366 T Mc M V₁ V₂ E →
        Res15367 T Mc M V₁ V₂ E → GoldLine153 T V₁ E s → Res15368 T Mc M E s

end CFSG.Quasithin

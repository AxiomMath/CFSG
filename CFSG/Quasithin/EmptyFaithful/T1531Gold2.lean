module

public import CFSG.Quasithin.EmptyFaithful.T1531Gold

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def IsDicksonEven153 {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (g : MulAut ↥V) : Prop :=
  letI : CommGroup ↥V := commGroupOfElemAbelian hV
  Even (rk (commV (Subgroup.zpowers g)))

structure Res15366B {G : Type} [Group G] (T Mc M V₁ V₂ E : Subgroup G) : Prop where
  barTE_eq : ∀ hV : IsElemAbelian 2 (VZ T M), ∀ g : MulAut ↥(VZ T M),
    g ∈ autOn (TE153 T E) (VZ T M) ↔ g ∈ autOn T (VZ T M) ∧ IsDicksonEven153 hV g
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

@[expose] def Stage15366B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ →
      Res15349 T Mc M V₁ → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E

@[expose] def Stage15367B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
      Res15350 T M → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E →
        Res15367 T Mc M V₁ V₂ E

@[expose] def Stage15368B : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
      Res15350 T M → LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E →
        Res15367 T Mc M V₁ V₂ E → GoldLine153 T V₁ E s → Res15368 T Mc M E s

end CFSG.Quasithin

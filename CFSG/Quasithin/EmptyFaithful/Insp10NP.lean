module

public import CFSG.Quasithin.EmptyFaithful.Insp10Top
public import CFSG.Quasithin.Background.S1567W4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def InspectIrrShape153 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
    LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E → Res15367 T Mc M V₁ V₂ E →
    GoldLine153 T V₁ E s → Res15368NoTwo T Mc M E s →
    F6.F618ConclusionCat
      (((G1_153 T Mc M E s).subgroupOf (G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))))
      (((G2_153 T E).subgroupOf (G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))) →
    IsInspList ↥(Xdot153 T Mc M E s) →
    ¬ Nonempty (↥(Xdot153 T Mc M E s) ≃* Equiv.Perm (Fin 3)) →
    oTwoUpper (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) ≤
      Xdot153 T Mc M E s →
    IrrShape153 T Mc M E s ∨
      Nonempty (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) ≃*
        ↥(StatedSL 3 (ZMod 2)))

theorem pCoreOf_G0_le_centralizer_VZ {G : Type} [Group G] [Finite G]
    {T Mc M V₁ V₂ E : Subgroup G} {t s : G} (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s)
    (h : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G)) :
    pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (VZ T M : Set G) := by
  intro q hq
  have hqT : q ∈ TE153 T E := S1567.pCore_G0_le_TE c L r66 r67 gl r68.triple hq
  have hF : q ∈ Subgroup.centralizer (FE153 E s : Set G) :=
    S1567.pCore_G0_le_centralizer_F c L r66 r67 gl r68.triple hq
  exact S1567.TE_inf_centralizer_E_F_le c L r66 gl ⟨⟨hqT, h hq⟩, hF⟩

theorem inspectRemainingNP_of_inputs (h113 : StageLemma14113) (hI : InspectIrrShape153)
    (hB : InspectB51Rem153) (hA : InspectA5Quot153) : InspectRemainingNP := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hconc hlist hS3 hO2 hL3 hscope
  have hirr : IrrShape153 T Mc M E s :=
    (hI G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hconc hlist hS3 hO2).resolve_right hL3
  have hC : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G) :=
    hscope.resolve_right (not_not.mpr hirr)
  have h2 := pCoreOf_G0_le_centralizer_VZ c L r66 r67 gl r68 hC
  exact inspectRemaining153_of_inputs h113 hB hA G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl
    (r68.toRes15368 h2) hconc hlist hS3 hO2

end CFSG.Quasithin

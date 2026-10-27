module

public import CFSG.Quasithin.EmptyFaithful.Insp10NP
public import CFSG.Quasithin.EmptyFaithful.Insp11A5
public import CFSG.Quasithin.EmptyFaithful.Insp11L3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def InspectIrrShapeL3 : Prop :=
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
    IrrShape153 T Mc M E s ∨ Nonempty (↥(Xdot153 T Mc M E s) ≃* ↥(StatedSL 3 (ZMod 2)))

theorem inspectIrrShape153_of_inputs (hI : InspectIrrShapeL3) (hL : InspectL3Normal153) :
    InspectIrrShape153 := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hconc hlist hS3 hO2
  rcases hI G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hconc hlist hS3 hO2 with h | he
  · exact Or.inl h
  · right
    obtain ⟨e⟩ := he
    have hA : IsGoldschmidtAmalgam
        (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G1_153 T Mc M E s))
        (barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (G2_153 T E)) := by
      rcases r68.triple.goldschmidt_mod_pPrimeCore with ⟨-, hA, -⟩ | ⟨-, -, -, -, hcyc⟩
      · exact hA
      · exfalso
        apply hcyc
        have hpc : Open.pCore 2 ↥(G0_153 T Mc M E s) = CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) :=
          Subgroup.map_injective (G0_153 T Mc M E s).subtype_injective r68.pCore_eq
        have hbot : (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map
            (QuotientGroup.mk' (Open.pCore 2 ↥(G0_153 T Mc M E s))) = ⊥ := by
          rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', hpc]
        rw [hbot]
        infer_instance
    have hnormal : (Xdot153 T Mc M E s).Normal :=
      barQ_thompsonJ_normal (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
    have htop := hL _ _ _ (Xdot153 T Mc M E s) hA hconc hnormal hO2 ⟨e⟩
    exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e⟩

theorem inspectRemainingNP_of_inputs₂ (h113 : StageLemma14113) (hI : InspectIrrShapeL3)
    (hL : InspectL3Normal153) (hB : InspectB51Rem153) (hG : A5HatGeom153) :
    InspectRemainingNP :=
  inspectRemainingNP_of_inputs h113 (inspectIrrShape153_of_inputs hI hL) hB
    (inspectA5Quot153_of_geom hG)

theorem inspectRemainingNP_of_inputs₃ (h113 : StageLemma14113)
    (hI : InspectIrrShapeL3) (hB : InspectB51Rem153) (hG : A5HatGeom153) : InspectRemainingNP :=
  inspectRemainingNP_of_inputs₂ h113 hI Insp11.inspectL3Normal153 hB hG

end CFSG.Quasithin

module

public import CFSG.Quasithin.Background.C1PackS15368
public import CFSG.Quasithin.Background.F6Cat
public import CFSG.Quasithin.Background.C1PackS15349
public import CFSG.Quasithin.EmptyFaithful.T1531In47
public import CFSG.Quasithin.EmptyFaithful.T1531In62
public import CFSG.Quasithin.EmptyFaithful.T1531In63
public import CFSG.Quasithin.EmptyFaithful.T1531In66b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace F6

variable {G : Type} [Group G] [Finite G] {I G₁ G₂ : Subgroup G}

theorem IsGoldschmidtTripleIn.f6_18Cat (hF : TheoremF618Cat) (h : IsGoldschmidtTripleIn I G₁ G₂)
    (hsq : SQTKTauCeti.StronglyQuasithin ↥I) (hK : CFSG.SectionRank.IsKGroupCat ↥I) :
    ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
          (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) =
        (G₁.subgroupOf I ⊓ G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ∧
      IsGoldschmidtAmalgam ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ∧
      IsAmalgamIso ((G₁.subgroupOf I).map (QuotientGroup.mk' (Open.pCore 2 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (Open.pCore 2 ↥I)))
        ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) ∧
      F618ConclusionCat ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
        ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))) ∨
    (pCoreOf 2 (G₁.subgroupOf I) = Open.pCore 2 ↥I ∧
      pCoreOf 2 (G₂.subgroupOf I) = Open.pCore 2 ↥I ∧
      Nonempty (↥I ⧸ CFSG.pPrimeCore 3 ↥I ≃* Equiv.Perm (Fin 3)) ∧
      G₁.subgroupOf I ⊔ CFSG.pPrimeCore 3 ↥I = ⊤ ∧
      ¬ IsCyclic ↥((CFSG.pPrimeCore 3 ↥I).map (QuotientGroup.mk' (Open.pCore 2 ↥I)))) := by
  rcases h.goldschmidt_mod_pPrimeCore with ⟨h₁, h₂, h₃⟩ | h'
  · exact Or.inl ⟨h₁, h₂, h₃, hF _ _ _ h₂.toIsGoldschmidtTriple
      ⟨↥I, inferInstance, inferInstance,
        ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mpr hsq, hK⟩, ⟨MulEquiv.refl _⟩⟩⟩
  · exact Or.inr h'

end F6

@[expose] def Stage1531InspectL2Sigma : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
    LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E → Res15367 T Mc M V₁ V₂ E →
    GoldLine153 T V₁ E s → Res15368 T Mc M E s →
    (∃ p : ℕ, p.Prime ∧
      F6.IsL2FieldExtCat p (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) →
    (F6.IsF618CaseEightCat
        (((G1_153 T Mc M E s).subgroupOf (G0_153 T Mc M E s)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))))
        (((G2_153 T E).subgroupOf (G0_153 T Mc M E s)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))) ∨
      F6.IsF618CaseNineCat
        (((G1_153 T Mc M E s).subgroupOf (G0_153 T Mc M E s)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))))
        (((G2_153 T E).subgroupOf (G0_153 T Mc M E s)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))) ∨
      F6.IsF618CaseEightCat
        (((G2_153 T E).subgroupOf (G0_153 T Mc M E s)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))))
        (((G1_153 T Mc M E s).subgroupOf (G0_153 T Mc M E s)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))) ∨
      F6.IsF618CaseNineCat
        (((G2_153 T E).subgroupOf (G0_153 T Mc M E s)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))))
        (((G1_153 T Mc M E s).subgroupOf (G0_153 T Mc M E s)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))))) →
    XE153 E = oTwoUpper (thompsonJ (G0_153 T Mc M E s)) ∨
      ¬ Group.IsSolvable ↥(thompsonJ (G0_153 T Mc M E s) ⊓ Subgroup.normalizer (V₁ : Set G))

@[expose] def Stage1531InspectBCat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
    LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E → Res15367 T Mc M V₁ V₂ E →
    GoldLine153 T V₁ E s → Res15368 T Mc M E s →
    F6.F618ConclusionCat
      (((G1_153 T Mc M E s).subgroupOf (G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))))
      (((G2_153 T E).subgroupOf (G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))) →
    XE153 E = oTwoUpper (thompsonJ (G0_153 T Mc M E s)) ∨
      ¬ Group.IsSolvable ↥(thompsonJ (G0_153 T Mc M E s) ⊓ Subgroup.normalizer (V₁ : Set G))

section Cases

variable {D : Type} [Group D] {H₁ H₂ : Subgroup D}

theorem isF618CaseOriented_or_of_cat (h : F6.IsF618CaseOrientedCat H₁ H₂) :
    F6.IsF618CaseOriented H₁ H₂ ∨
      ((∃ p : ℕ, p.Prime ∧ F6.IsL2FieldExtCat p D) ∧
        (F6.IsF618CaseEightCat H₁ H₂ ∨ F6.IsF618CaseNineCat H₁ H₂)) := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · rcases h.1 with hS | ⟨p, hp, -, hL⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨Or.inl hS, h.2.1, h.2.2.1, h.2.2.2⟩))))))))
    · exact Or.inr ⟨⟨p, hp, hL⟩, Or.inl h⟩
  · rcases h.1 with hS | hS | ⟨p, hp, -, hL⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨Or.inl hS, h.2.1, h.2.2.1, h.2.2.2⟩)))))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨Or.inr hS, h.2.1, h.2.2.1, h.2.2.2⟩)))))))))
    · exact Or.inr ⟨⟨p, hp, hL⟩, Or.inr h⟩
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h)))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl h))))))))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr h))))))))))))

end Cases

theorem stage1531InspectBCat_of (hI : Stage1531InspectB) (hL : Stage1531InspectL2Sigma) :
    Stage1531InspectBCat := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hconc
  rcases hconc with h | h
  · rcases isF618CaseOriented_or_of_cat h with h' | ⟨hp, h8 | h9⟩
    · exact hI G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 (Or.inl h')
    · exact hL G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hp (Or.inl h8)
    · exact hL G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hp (Or.inr (Or.inl h9))
  · rcases isF618CaseOriented_or_of_cat h with h' | ⟨hp, h8 | h9⟩
    · exact hI G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 (Or.inr h')
    · exact hL G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hp (Or.inr (Or.inr (Or.inl h8)))
    · exact hL G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hp (Or.inr (Or.inr (Or.inr h9)))

section Geometry

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem closing_153C (hF : F6.TheoremF618Cat) (hI : Stage1531InspectBCat)
    (c : Ctx153 G T Mc M V₁ V₂ t) (r45 : Res15345 T Mc M V₁ V₂) (r46 : Res15346 T M V₁ V₂)
    (r49 : Res15349 T Mc M V₁) (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) (r68 : Res15368 T Mc M E s) :
    False := by
  have hne : pCoreOf 2 (G0_153 T Mc M E s) ≠ ⊥ := by
    intro hbot
    have h0 : VZ T M ≤ ⊥ := hbot ▸ r68.V_le_pCore
    have h16 := c.hyp.card_VZ
    rw [le_bot_iff.mp h0, Subgroup.card_bot] at h16
    omega
  have hq := stronglyQuasithin_of_pCoreOf_ne_bot c.hyp.qtfe.qtke hne
  have hk := kGroup_of_pCoreOf_ne_bot c.hyp.qtfe.qtke c.hyp.qtfe.simple c.hyp.qtfe.nonabelian hne
  rcases r68.triple.f6_18Cat hF hq hk with ⟨-, -, -, hconc⟩ | ⟨-, -, -, -, hcyc⟩
  · rcases hI G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hconc with hA | hB
    · exact false_of_XE_eqB c r46 L r66 r67 gl hA
    · exact false_of_nonsolvable c r45 r49 r67 hB
  · apply hcyc
    have hpc : Open.pCore 2 ↥(G0_153 T Mc M E s) = CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) :=
      Subgroup.map_injective (G0_153 T Mc M E s).subtype_injective r68.pCore_eq
    have hbot : (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (Open.pCore 2 ↥(G0_153 T Mc M E s))) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', hpc]
    rw [hbot]
    infer_instance

end Geometry

theorem stageTheorem1531_of_inputsCat (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hF : F6.TheoremF618Cat) (i44 : Stage15344) (i46 : Stage15346Four) (i49c : Stage15349Core)
    (i50 : Stage15350) (i65 : Stage15365One) (i67r : Stage15367Rest) (i68t : Stage15368Two)
    (iI : Stage1531InspectBCat) : StageTheorem1531 := by
  have i46' : Stage15346 := stage15346_of_four i46
  have i47 : Stage15347 := stage15347
  have i48 : Stage15348 := stage15348 h11 h113
  have i49 : Stage15349 := stage15349_of_core h11 h113 i49c
  have i62 : Stage15362 := stage15362 h11
  have i63 : Stage15363 := stage15363
  have i66 : Stage15366B := stage15366B h11 h113
  have i67 : Stage15367B := stage15367B_of_rest h113 i67r
  have i68 : Stage15368B := stage15368B_of_rest2 h113 (stage15368Rest2_of_two h113 i68t)
  intro G _ _ T Mc M hq hMf hO
  have h : Hyp153 G T Mc M := ⟨hq, hMf, hO⟩
  obtain ⟨V₁, V₂, t, D⟩ := h.exists_decomp
  have c : Ctx153 G T Mc M V₁ V₂ t := ⟨h, D⟩
  have r45 := lemma_15_3_45 i44 h113 c
  have r46 := i46' G T Mc M V₁ V₂ t c r45
  have r47 := i47 G T Mc M V₁ V₂ t c r45 r46
  have r48 := i48 G T Mc M V₁ V₂ t c r45 r46 r47
  have r49 := i49 G T Mc M V₁ V₂ t c r45 r46 r47 r48
  have hF91 : ∀ H : Subgroup G, IsHTM153 T M H →
      HypF91 T (VZ T M) (Y153 Mc M) (quasithinOmegaOneCenter T) (ZS153 T M V₁) H :=
    fun H hH => hypF91_of_stage15348 i48 c r45 r46 r47 r49 hH
  have r50 := i50 G T Mc M V₁ V₂ t c r45 r46 r47 r49 hF91
  have r62 := i62 G T Mc M V₁ V₂ t c r45 r46 r50
  have r63 := i63 G T Mc M V₁ V₂ t c r45 r46 r50 r62
  have r64 := lemma_15_3_64 c r47 r62
  have r65 := i65 G T Mc M V₁ V₂ t c r45 r46 r50 r49 r62 r63 r64
  have r65two := lemma_15_3_65_two c r46 r63 r65
  obtain ⟨E, L⟩ := exists_lineData153 c r46 r65two
  have r66 := i66 G T Mc M V₁ V₂ E t c r45 r46 r49 L
  have r67 := i67 G T Mc M V₁ V₂ E t c r45 r46 r49 r50 L r66
  obtain ⟨s, gl⟩ := exists_goldLine153B h D r66
  have r68 := i68 G T Mc M V₁ V₂ E t s c r45 r46 r49 r50 L r66 r67 gl
  exact (closing_153C hF iI c r45 r46 r49 L r66 r67 gl r68).elim

end CFSG.Quasithin

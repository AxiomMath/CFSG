module

public import CFSG.LocalAnalysis.StandardType.GGHypThreeSixteenFlatMarking
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummand

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Generic

variable {X : Type} [Group X] [Finite X]

@[expose] def GGAutKConfigFlat (p : ℕ) (V E K : Subgroup X) : Prop :=
  ∃ (W' : Type) (_ : Group W') (_ : Finite W') (π : ↥(E ⊔ K) →* W'),
    Function.Surjective π ∧
    π.ker ≤ ((E ⊔ (K ⊓ V)) ⊓ Subgroup.centralizer (K : Set X)).subgroupOf (E ⊔ K) ∧
    GGHypThreeSixteenRestFlat p (((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map π)
      ((E.subgroupOf (E ⊔ K)).map π) ∧
    LargeEvenLayer (⊤ : Subgroup (GGHypQuot (((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map π))) ≠ ⊥ ∧
    ¬ GGFusionException p (((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map π)
      ((E.subgroupOf (E ⊔ K)).map π)

theorem ggAutKConfigFlat_le (hKF : GGKGroupFusionLayerInputFlat) (hX : CFSG.Open.IsKGroup X)
    {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {V E : Subgroup X} (hfus : GGControlsStrongFusion V E) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2) (hO : LargeEvenPPrimeCore p X ≤ V) {K : Subgroup X}
    (hK : CFSG.IsComponent K) (hconf : ¬ K ≤ V → GGAutKConfigFlat p V E K) : K ≤ V := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hKV
  have hKp : p ∣ Nat.card K := by
    by_contra hnd
    exact hKV ((ggLe_pPrimeCore_of_isSubnormal hK.2 hnd).trans hO)
  have hnorm := ggLemmaThreeThirteen_top hfus hE hEcard hK hKp hKV
  obtain ⟨W', _, _, π, hπ, hker, hrest, hlayer, hexc⟩ := hconf hKV
  have hyp := And.intro (ggAutK_hypOne hp hp2 hfus hE hEcard hnorm hKV π hπ hker) hrest
  rcases hKF W' ((hX.subgroup (E ⊔ K)).of_surjective π hπ) p _ _ hyp hlayer with htop | hex
  · have hker' : π.ker ≤ (E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K) := fun w hw =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hker hw))).1
    exact hKV ((le_sup_right.trans (ggAutK_le_of_map_eq_top π hker' htop)).trans
      (sup_le hfus.1 inf_le_right))
  · exact hexc hex

end Generic

section Layer

variable {X : Type} [Group X]

@[expose] def GGHypRestIIIad (H E : Subgroup X) : Prop :=
  (∀ C : Subgroup (GGHypQuot H), IsComponentOf C ⊤ →
    ggHypImage H E ≤ Subgroup.normalizer (C : Set (GGHypQuot H)) ∧
      LargeEvenMarking ↥C (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ e ∈ ggHypImage H E, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : GGHypQuot H) = e⁻¹ * l * e) φ)) ∧
  (commutator ↥(ggHypLayer H) = ⊤ ∨ LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) = ⊥) ∧
  (∃ k : ℕ, derivedSeries ↥H k ≤ (ggHypLayer H).subgroupOf H)

theorem ggHypRestIIIFlat_of_ad [Finite X] {p : ℕ} {H E : Subgroup X} (h : GGHypRestIIIad H E)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥) : GGHypRestIIIFlat p H E :=
  ⟨h.1, h.2.1, h.2.2, fun hb => absurd hb hL⟩

@[expose] def GGRCSAutKIIIFlat (V E K : Subgroup X) : Prop :=
  ∀ [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal], GGHypRestIIIad
    (((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map
      (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))))
    ((E.subgroupOf (E ⊔ K)).map (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))))

@[expose] def GGRCSAutKIVFlat [Finite X] (p : ℕ) (V E K : Subgroup X) : Prop :=
  ∀ [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal], GGHypRestIVFlat p
    ((E.subgroupOf (E ⊔ K)).map (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))))

theorem ggRCS_autKConfigFlat [Finite X] {p : ℕ} (hp : p.Prime) {V E K S : Subgroup X}
    (hfus : GGControlsStrongFusion V E) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) (hK : CFSG.IsComponent K)
    (hcat : InCatalog (↥K ⧸ Subgroup.center ↥K)) (hS : GGRCSQuasiPiece p V S) (hSK : S ≤ K)
    (h3 : GGRCSAutKIIIFlat V E K) (h4 : GGRCSAutKIVFlat p V E K)
    (hexc : GGRCSAutKNotExc p V E K) : GGAutKConfigFlat p V E K := by
  have : Fact p.Prime := ⟨hp⟩
  have hN := ggRCSU_normal (V := V) hEK
  refine ⟨_, inferInstance, inferInstance, QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)),
    QuotientGroup.mk'_surjective _, ?_,
    ggHypThreeSixteenRestFlat_of_parts (ggRCS_hypRestII hfus hE hEcard hEK hK hcat)
      (ggHypRestIIIFlat_of_ad (@h3 hN) (ggRCS_layer_ne_bot hp hfus.1 hS hSK)) (@h4 hN),
    ggRCS_layer_ne_bot hp hfus.1 hS hSK, @hexc hN⟩
  intro w hw
  rw [QuotientGroup.ker_mk'] at hw
  exact hw

end Layer

section Inputs

@[expose] def GGRootCentAutKIIIFlatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        ∀ K S : Subgroup (GGRCSNbar r),
          GGRCSAutKSetting p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K S →
            GGRCSAutKIIIFlat (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K

@[expose] def GGRootCentAutKIVFlatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        ∀ K S : Subgroup (GGRCSNbar r),
          GGRCSAutKSetting p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K S →
            GGRCSAutKIVFlat p (ggRCSImg r (ggM p B x L D J)) (ggRCSImg r E) K

@[expose] def GGSixRootCentralizerSummandFlatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        ∃ 𝒮 : Set (Subgroup (↥(Subgroup.centralizer {r}) ⧸
            CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}))),
          (∀ S ∈ 𝒮,
            (∃ R : Subgroup (↥(Subgroup.centralizer {r}) ⧸
                CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r})), R.Normal ∧
                IsPGroup p ↥(R.map (QuotientGroup.mk' (LargeEvenPPrimeCore p
                  (↥(Subgroup.centralizer {r}) ⧸
                    CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}))))) ∧
                S ≤ R) ∨
              ∃ K : Subgroup (↥(Subgroup.centralizer {r}) ⧸
                  CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r})), S ≤ K ∧
                IsComponentOf (K.map (QuotientGroup.mk' (LargeEvenPPrimeCore p
                  (↥(Subgroup.centralizer {r}) ⧸
                    CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}))))) ⊤ ∧
                (¬ K ≤ ((ggM p B x L D J).subgroupOf (Subgroup.centralizer {r})).map
                    (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}))) →
                  CFSG.IsComponent K ∧ GGAutKConfigFlat p
                    (((ggM p B x L D J).subgroupOf (Subgroup.centralizer {r})).map
                      (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}))))
                    ((E.subgroupOf (Subgroup.centralizer {r})).map
                      (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}))))
                    K)) ∧
          ∀ y : ↥(Subgroup.centralizer {r}),
            (y : G) ∈ ggOTwoPrime (ggG0 p B x L D J ⊓ Subgroup.centralizer {r}) →
              (y : G) ^ p = 1 → QuotientGroup.mk' _ y ∈ sSup 𝒮

theorem ggSixRootCentralizerPiecesInput_of_summandsFlat (hKF : GGKGroupFusionLayerInputFlat)
    (h : GGSixRootCentralizerSummandFlatInput) : GGSixRootCentralizerPiecesInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  obtain ⟨𝒮, h𝒮, hcov⟩ := h G p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have hfus := ggSixRootCentralizer_quotientFusion hctx hch
  have hO := ggSixRootCentralizer_pPrimeCore_le hctx hch
  have hEr := hch.le_centralizer
  have hr1 : r ≠ 1 := by
    intro h
    have h2 := hch.2.2.2.2.1
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hXK : CFSG.Open.IsKGroup (GGRCSNbar r) :=
    (CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup hctx.1.2.2.1 _
      (ggStepTwo_centralizer_ne_top hctx.1.2.1 hr1)).quotient _
  obtain ⟨-, hE, hEcard, -⟩ := hch
  obtain ⟨hEel, hEc⟩ := ggBarE_elem_card hp hp2 hEr hE
  set Vb := ((ggM p B x L D J).subgroupOf (Subgroup.centralizer {r})).map
    (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}))) with hVb
  have hle : sSup 𝒮 ≤ sSup {T | GGSubnormalPiece p Vb T} := by
    refine sSup_le fun S hS => ?_
    obtain ⟨R, hRn, hRp, hSR⟩ | ⟨K, hSK, hKc, hKV⟩ := h𝒮 S hS
    · have hRV : R ≤ Vb :=
        ggLe_of_isPGroup_map_pPrimeCore hp hfus hEel (hEc.trans hEcard) hO hRn hRp
      exact hSR.trans (le_sSup ⟨hRV, Or.inr ⟨R, hRn, hRV, le_rfl⟩⟩)
    · have hKle : K ≤ Vb := by
        by_cases hK : K ≤ Vb
        · exact hK
        · exact ggAutKConfigFlat_le hKF hXK hp hp2 hfus hEel (hEc.trans hEcard) hO (hKV hK).1
            fun h' => (hKV h').2
      exact hSK.trans (le_sSup ⟨hKle, Or.inl hKc⟩)
  exact ⟨{T | GGSubnormalPiece p Vb T}, fun T hT => hT, fun y hy hyp => hle (hcov y hy hyp)⟩

theorem ggSixRootCentralizerQuotientInput_of_summandsFlat (hKF : GGKGroupFusionLayerInputFlat)
    (h : GGSixRootCentralizerSummandFlatInput) : GGSixRootCentralizerQuotientInput :=
  ggSixRootCentralizerQuotientInput_of_pieces
    (ggSixRootCentralizerPiecesInput_of_summandsFlat hKF h)

end Inputs

end CFSG.StandardType

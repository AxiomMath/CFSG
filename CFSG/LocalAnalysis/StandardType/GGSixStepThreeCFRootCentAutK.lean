module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFRootCent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Generic

variable {X : Type} [Group X] [Finite X]

@[expose] def GGAutKConfig (p : ℕ) (V E K : Subgroup X) : Prop :=
  ∃ (W' : Type) (_ : Group W') (_ : Finite W') (π : ↥(E ⊔ K) →* W'),
    Function.Surjective π ∧
    π.ker ≤ ((E ⊔ (K ⊓ V)) ⊓ Subgroup.centralizer (K : Set X)).subgroupOf (E ⊔ K) ∧
    GGHypThreeSixteenRest p (((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map π)
      ((E.subgroupOf (E ⊔ K)).map π) ∧
    LargeEvenLayer (⊤ : Subgroup (GGHypQuot (((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map π))) ≠ ⊥ ∧
    ¬ GGFusionException p (((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map π)
      ((E.subgroupOf (E ⊔ K)).map π)

theorem ggAutKConfig_le (hKF : GGKGroupFusionLayerInput) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {V E : Subgroup X} (hfus : GGControlsStrongFusion V E) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2) (hO : LargeEvenPPrimeCore p X ≤ V) {K : Subgroup X}
    (hK : CFSG.IsComponent K) (hconf : ¬ K ≤ V → GGAutKConfig p V E K) : K ≤ V := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hKV
  have hKp : p ∣ Nat.card K := by
    by_contra hnd
    exact hKV ((ggLe_pPrimeCore_of_isSubnormal hK.2 hnd).trans hO)
  have hnorm := ggLemmaThreeThirteen_top hfus hE hEcard hK hKp hKV
  obtain ⟨W', _, _, π, hπ, hker, hrest, hlayer, hexc⟩ := hconf hKV
  have hyp := And.intro (ggAutK_hypOne hp hp2 hfus hE hEcard hnorm hKV π hπ hker) hrest
  rcases hKF W' p _ _ hyp hlayer with htop | hex
  · have hker' : π.ker ≤ (E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K) := fun w hw =>
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hker hw))).1
    exact hKV ((le_sup_right.trans (ggAutK_le_of_map_eq_top π hker' htop)).trans
      (sup_le hfus.1 inf_le_right))
  · exact hexc hex

theorem ggLe_of_isPGroup_map_pPrimeCore {p : ℕ} (hp : p.Prime) {V E : Subgroup X}
    (hfus : GGControlsStrongFusion V E) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hO : LargeEvenPPrimeCore p X ≤ V) {R : Subgroup X} (hR : R.Normal)
    (hRp : IsPGroup p ↥(R.map (QuotientGroup.mk' (LargeEvenPPrimeCore p X)))) : R ≤ V := by
  have : Fact p.Prime := ⟨hp⟩
  set O := LargeEvenPPrimeCore p X
  set π := QuotientGroup.mk' O
  have hcomapV : (V.map π).comap π = V := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hO]
  have hfus' : GGControlsStrongFusion (V.map π) (E.map π) := by
    rw [ggControlsStrongFusion_iff]
    refine ⟨Subgroup.map_mono hfus.1, ?_⟩
    rintro _ ⟨e, he, rfl⟩ he1 g' hg'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O g'
    have he1' : e ≠ 1 := fun h => he1 (by rw [h, map_one])
    have hgV : g⁻¹ * e * g ∈ V := by
      have h1 : π (g⁻¹ * e * g) ∈ V.map π := by
        rw [map_mul, map_mul, map_inv]
        exact hg'
      rw [← Subgroup.mem_comap, hcomapV] at h1
      exact h1
    exact Subgroup.mem_map_of_mem π (hfus.mem_of_conj_mem he he1' hgV)
  have hcop : Nat.Coprime p (Nat.card O) := CFSG.pPrimeCore_coprime_card
  have hinj : Function.Injective (π.comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hs
    have hsO : (s : X) ∈ O := by
      rw [← QuotientGroup.ker_mk' O]
      exact hs
    have h1 : orderOf (s : X) = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one (hE.2 _ s.2)) hcop)
        (Subgroup.orderOf_dvd_natCard O hsO)
    rw [Subgroup.mem_bot]
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  have hmap : E.map π = (π.comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hEcard' : Nat.card (E.map π) = p ^ 2 := by
    rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hEcard]
  have hpc := hfus'.pCore_le hp (ggIsElemAbelian_map hE π) hEcard' p
  have hRle : R.map π ≤ CFSG.pCore p (X ⧸ O) :=
    le_sSup ⟨hR.map π (QuotientGroup.mk'_surjective O), hRp⟩
  calc R ≤ (R.map π).comap π := Subgroup.le_comap_map π R
    _ ≤ (V.map π).comap π := Subgroup.comap_mono (hRle.trans hpc)
    _ = V := hcomapV

end Generic

section Inputs

@[expose] def GGSixRootCentralizerSummandInput : Prop :=
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
                  CFSG.IsComponent K ∧ GGAutKConfig p
                    (((ggM p B x L D J).subgroupOf (Subgroup.centralizer {r})).map
                      (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}))))
                    ((E.subgroupOf (Subgroup.centralizer {r})).map
                      (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}))))
                    K)) ∧
          ∀ y : ↥(Subgroup.centralizer {r}),
            (y : G) ∈ ggOTwoPrime (ggG0 p B x L D J ⊓ Subgroup.centralizer {r}) →
              (y : G) ^ p = 1 → QuotientGroup.mk' _ y ∈ sSup 𝒮

theorem ggSixRootCentralizerPiecesInput_of_summands (hKF : GGKGroupFusionLayerInput)
    (h : GGSixRootCentralizerSummandInput) : GGSixRootCentralizerPiecesInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  obtain ⟨𝒮, h𝒮, hcov⟩ := h G p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have hfus := ggSixRootCentralizer_quotientFusion hctx hch
  have hO := ggSixRootCentralizer_pPrimeCore_le hctx hch
  have hEr := hch.le_centralizer
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
        · exact ggAutKConfig_le hKF hp hp2 hfus hEel (hEc.trans hEcard) hO (hKV hK).1
            fun h' => (hKV h').2
      exact hSK.trans (le_sSup ⟨hKle, Or.inl hKc⟩)
  exact ⟨{T | GGSubnormalPiece p Vb T}, fun T hT => hT, fun y hy hyp => hle (hcov y hy hyp)⟩

theorem ggSixRootCentralizerQuotientInput_of_summands (hKF : GGKGroupFusionLayerInput)
    (h : GGSixRootCentralizerSummandInput) : GGSixRootCentralizerQuotientInput :=
  ggSixRootCentralizerQuotientInput_of_pieces (ggSixRootCentralizerPiecesInput_of_summands hKF h)

theorem ggSixStepThreeBInput_of_summands (hcyc : GGRootCentralizerCyclicInput)
    (hKF : GGKGroupFusionLayerInput) (h : GGSixRootCentralizerSummandInput) :
    GGSixStepThreeBInput :=
  ggSixStepThreeBInput_of_quotient hcyc (ggSixRootCentralizerQuotientInput_of_summands hKF h)

end Inputs

end CFSG.StandardType

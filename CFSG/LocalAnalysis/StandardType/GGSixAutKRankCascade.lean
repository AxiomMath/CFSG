module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKRankDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatSeventeen

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Stage0

@[expose] def GGSixAutKHypRestAtFlatInputRk : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ b ∈ Bs, b ≠ 1 → ∀ L₁ : Subgroup G,
      IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
      GGAutKRank p Bs t f L₁ →
      ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {b}) → L₁ ≤ K →
        ¬ K ≤ ggM p B x L D J →
        ∀ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} →
          ∃ (W' : Type) (_ : Group W') (_ : Finite W') (π : ↥(ggAutKW D K m) →* W'),
            Function.Surjective π ∧
            π.ker ≤ (ggAutKH D K (ggM p B x L D J) m ⊓
              Subgroup.centralizer (K : Set G)).subgroupOf (ggAutKW D K m) ∧
            GGHypThreeSixteenRestFlat p
              (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map π)
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π)

theorem ggSixAutKHypRestAtFlatInputRk_of_canon (h2 : GGAutKCanonIIInput)
    (h3 : GGAutKCanonIIIFlatInputRk) (h4 : GGAutKCanonIVCompInput) :
    GGSixAutKHypRestAtFlatInputRk := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 b hb hb1 L₁ hL₁ hrk K hK hLK hKM m hm hEC
  have hcfg : GGAutKConjConfig p B Bs x L D J b L₁ K m := ⟨hb, hb1, hL₁, hK, hLK, hKM, hm, hEC⟩
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨-, ⟨⟨-, hDel, hDcard, -⟩, -⟩, -⟩ := hctx.2
  have hfusE : GGControlsStrongFusion (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) := by
    refine s1.2.1.of_map_conj_le ((ggM p B x L D J).inv_mem hm) ?_
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  have hE0el : IsElemAbelian p (D.map (MulAut.conj m⁻¹).toMonoidHom) :=
    isElemAbelian_map_hom hDel _
  have hE0card : Nat.card (D.map (MulAut.conj m⁻¹).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hDcard]
  have hnorm : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    ggLemmaThreeThirteenInput_holds G p hp hp2 (Subgroup.centralizer {b})
      (ggM p B x L D J ⊓ Subgroup.centralizer {b}) _
      (ggStepTwo_kGroup_of_ne_top hctx.1.2.2.1 (ggStepTwo_centralizer_ne_top hctx.1.2.1 hb1))
      hE0el hE0card (hfusE.inf_in hEC) K hK (fun h => hKM (h.trans inf_le_left))
  have hN := ggAutKV_normal (M := ggM p B x L D J) hnorm
  refine ⟨_, inferInstance, inferInstance, ggAutKPi D K (ggM p B x L D J) m,
    QuotientGroup.mk'_surjective _, ?_, ggHypThreeSixteenRestFlat_of_parts
      (h2 G p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg)
      (h3 G p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg hrk)
      (ggHypRestIVFlat_of_componentwise
        (h4 G p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg))⟩
  intro w hw
  rw [ggAutKPi, QuotientGroup.ker_mk'] at hw
  exact hw

theorem ggStepTwoAutKRestFlatInput_of_finerRk (hR : GGSixAutKHypRestAtFlatInputRk)
    (h5 : GGStepTwoAutKFiveInput) (h3 : GGStepTwoAutKThreeInput) :
    GGStepTwoAutKRestFlatInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair K hK hLK hKM
  have hchoice : ∃ m ∈ ggM p B x L D J,
      D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} ∧
      (p = 3 → GGStepTwoExcThreeType L₁ → ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
        g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
        Nat.Coprime (orderOf g) p) := by
    by_cases hT : p = 3 ∧ GGStepTwoExcThreeType L₁
    · obtain ⟨m, hm, hmC, hg⟩ :=
        h3 G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair K hK hLK hKM hT.1 hT.2
      exact ⟨m, hm, hmC, fun _ _ => hg⟩
    · obtain ⟨⟨hBBs, hBsEl, -⟩, ⟨⟨hDB, -⟩, -⟩, -⟩ := hctx.2
      exact ⟨1, (ggM p B x L D J).one_mem,
        ggStepTwo_map_conj_one_le hBsEl (hDB.trans hBBs) hpair.1,
        fun hp3 hT' => absurd ⟨hp3, hT'⟩ hT⟩
  obtain ⟨m, hm, hEC, hgchoice⟩ := hchoice
  obtain ⟨W', _, _, π, hπ, hker, hrest⟩ :=
    hR G p B Bs x L D J t n f ψ hctx s1 b hpair.1 hpair.2.1 L₁ hpair.2.2.1
      (Or.inl hpair.2.2.2) K hK hLK hKM m hm hEC
  refine ⟨m, hm, hEC, W', inferInstance, inferInstance, π, hπ, hker, hrest, fun hex => ?_⟩
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨-, ⟨⟨-, hDel, hDcard, -⟩, -⟩, -⟩ := hctx.2
  have hfusE : GGControlsStrongFusion (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) := by
    refine s1.2.1.of_map_conj_le ((ggM p B x L D J).inv_mem hm) ?_
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  have hE0el : IsElemAbelian p (D.map (MulAut.conj m⁻¹).toMonoidHom) :=
    isElemAbelian_map_hom hDel _
  have hE0card : Nat.card (D.map (MulAut.conj m⁻¹).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hDcard]
  have hnorm : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    ggLemmaThreeThirteenInput_holds G p hp hp2 (Subgroup.centralizer {b})
      (ggM p B x L D J ⊓ Subgroup.centralizer {b}) _
      (ggStepTwo_kGroup_of_ne_top hctx.1.2.2.1
        (ggStepTwo_centralizer_ne_top hctx.1.2.1 hpair.2.1))
      hE0el hE0card (hfusE.inf_in hEC) K hK (fun h => hKM (h.trans inf_le_left))
  have hEM : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ ggM p B x L D J := hfusE.1
  have hH₀C : D.map (MulAut.conj m⁻¹).toMonoidHom ⊔ (K ⊓ ggM p B x L D J) ≤
      ggM p B x L D J ⊓ Subgroup.centralizer {b} :=
    sup_le (le_inf hEM hEC) (le_inf inf_le_right (inf_le_left.trans hK.1))
  obtain ⟨hC, he⟩ := ggAutK_image_component hpair.isComponentOf_inf hLK hpair.le_ggM hH₀C
    hK.2.2 hnorm π hπ hker
  rcases ggFusionException_of_component hC he hex with ⟨hp3, hT, hpg⟩ | ⟨hp5, hT⟩
  · obtain ⟨g, hgL, hgZ, hgE, hgp⟩ := hgchoice hp3 hT
    exact ggAutK_not_isPGroup hpair.isComponentOf_inf hLK hpair.le_ggM hH₀C hK.2.2 hnorm π hπ
      hker hgL hgZ hgE hgp hpg
  · exact h5 G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair K hK hLK hKM hp5 hT

theorem ggStepTwoAutKRestFlatInput_of_round9Rk (h3 : GGAutKCanonIIIFlatInputRk)
    (h4 : GGAutKCanonIVCompInput) (hF : GGSixFieldFiveInput) (hD : GGLayerNotDFourTwoRound9)
    (hU : GGLayerNotUFourAltSixRound9) (h2 : GGStepTwoChoiceThreeTwoRest) :
    GGStepTwoAutKRestFlatInput :=
  have hD7 := ggLayerNotDFourTwoRound7_of_exc hD.1 hD.2.1 hD.2.2.1 hD.2.2.2.1 hD.2.2.2.2
  have hUA := ggLayerNotUFourAltSixRest_of_exc hU.1 hU.2.1 hU.2.2.1 hU.2.2.2.1 hU.2.2.2.2
  ggStepTwoAutKRestFlatInput_of_finerRk
    (ggSixAutKHypRestAtFlatInputRk_of_canon ggAutKCanonIIInput_holds h3 h4)
    (ggStepTwoAutKFiveInput_of_tailTags hF hD7.1 hD7.2.1 hD7.2.2.1 hD7.2.2.2.1 hD7.2.2.2.2.1
      hD7.2.2.2.2.2.1 hD7.2.2.2.2.2.2.1 hD7.2.2.2.2.2.2.2.1 hD7.2.2.2.2.2.2.2.2)
    (ggStepTwoAutKThreeInput_of_choice (ggStepTwoChoiceThreeInput_of_remaining hD7 hUA h2))

@[expose] def GGSixAutKHypRestFlatInputRk : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ b ∈ Bs, b ≠ 1 → ∀ L₁ : Subgroup G,
      IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
      GGAutKRank p Bs t f L₁ →
      ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {b}) → L₁ ≤ K →
        ¬ K ≤ ggM p B x L D J →
        ∃ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} ∧
          ∃ (W' : Type) (_ : Group W') (_ : Finite W') (π : ↥(ggAutKW D K m) →* W'),
            Function.Surjective π ∧
            π.ker ≤ (ggAutKH D K (ggM p B x L D J) m ⊓
              Subgroup.centralizer (K : Set G)).subgroupOf (ggAutKW D K m) ∧
            GGHypThreeSixteenRestFlat p
              (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map π)
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π)

theorem ggSixAutKHypRestFlatInputRk_of_at (h : GGSixAutKHypRestAtFlatInputRk) :
    GGSixAutKHypRestFlatInputRk := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 b hb hb1 L₁ hL₁ hrk K hK hLK hKM
  obtain ⟨⟨hBBs, hBsEl, -⟩, ⟨⟨hDB, -⟩, -⟩, -⟩ := hctx.2
  have hD := ggStepTwo_map_conj_one_le hBsEl (hDB.trans hBBs) hb
  exact ⟨1, (ggM p B x L D J).one_mem, hD,
    h G p B Bs x L D J t n f ψ hctx s1 b hb hb1 L₁ hL₁ hrk K hK hLK hKM 1
      (ggM p B x L D J).one_mem hD⟩

section Seventeen

theorem ggSixSeventeenAutKFlatInput_of_restRk
    (hR : GGSixAutKHypRestFlatInputRk) : GGSixSeventeenAutKFlatInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 b L₁ hpair K hK hLK hKM
  obtain ⟨m, hm, hEC, W', _, _, π, hπ, hker, hrest⟩ :=
    hR G p B Bs x L D J t n f ψ hctx s1 b hpair.1 hpair.2.1 L₁ hpair.2.2.1
      (Or.inr hpair.2.2.2) K hK hLK hKM
  refine ⟨m, hm, hEC, W', inferInstance, inferInstance, π, hπ, hker, hrest, ?_⟩
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨-, ⟨⟨-, hDel, hDcard, -⟩, -⟩, -⟩ := hctx.2
  have hfusE : GGControlsStrongFusion (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) := by
    refine s1.2.1.of_map_conj_le ((ggM p B x L D J).inv_mem hm) ?_
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  have hE0el : IsElemAbelian p (D.map (MulAut.conj m⁻¹).toMonoidHom) :=
    isElemAbelian_map_hom hDel _
  have hE0card : Nat.card (D.map (MulAut.conj m⁻¹).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hDcard]
  have hnorm : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    ggLemmaThreeThirteenInput_holds G p hp hp2 (Subgroup.centralizer {b})
      (ggM p B x L D J ⊓ Subgroup.centralizer {b}) _
      (ggStepTwo_kGroup_of_ne_top hctx.1.2.2.1
        (ggStepTwo_centralizer_ne_top hctx.1.2.1 hpair.2.1))
      hE0el hE0card (hfusE.inf_in hEC) K hK (fun h => hKM (h.trans inf_le_left))
  have hEM : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ ggM p B x L D J := hfusE.1
  have hH₀C : D.map (MulAut.conj m⁻¹).toMonoidHom ⊔ (K ⊓ ggM p B x L D J) ≤
      ggM p B x L D J ⊓ Subgroup.centralizer {b} :=
    sup_le (le_inf hEM hEC) (le_inf inf_le_right (inf_le_left.trans hK.1))
  obtain ⟨hC, he⟩ := ggAutK_image_component hpair.isComponentOf_inf hLK hpair.le_ggM hH₀C
    hK.2.2 hnorm π hπ hker
  exact ggSixSeventeen_not_fusionException hpair.2.2.2 hC he

theorem ggSixLemmaSixSeventeenInput_of_restFlatRk
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor InCatalog)
    (hKF : GGKGroupFusionLayerInputFlat) (hR : GGSixAutKHypRestFlatInputRk)
    (hW : GGSixSeventeenWitnessInputFor fun _ => True)
    (h610 : GGSixBstarUniqueV2Input) (h611 : GGSixLSixElevenInput)
    (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (hlin : GGSixSeventeenLinearTypeInput) : GGSixLemmaSixSeventeenInput :=
  ggSixLemmaSixSeventeenInput_of_schreierFlat hSch hKF (ggSixSeventeenAutKFlatInput_of_restRk hR)
    hW h610 h611 h612 h613t hlin

end Seventeen

end Stage0

end CFSG.StandardType

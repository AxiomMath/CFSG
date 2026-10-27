module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatStepTwo
public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeenTable

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGSixAutKHypRestFlatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ b ∈ Bs, b ≠ 1 → ∀ L₁ : Subgroup G,
      IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
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

@[expose] def GGSixSeventeenAutKFlatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), GGSixSeventeenPair p B Bs x L D J t f b L₁ →
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
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π) ∧
            ¬ GGFusionException p
              (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map π)
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π)

end Inputs

section Steps

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}

theorem ggSixSeventeenComponentFlat_le (hKF : GGKGroupFusionLayerInputFlat)
    (hR : GGSixSeventeenAutKFlatInput) (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) {b : G} {L₁ : Subgroup G}
    (hpair : GGSixSeventeenPair p B Bs x L D J t f b L₁) {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer {b})) (hLK : L₁ ≤ K) :
    K ≤ ggM p B x L D J := by
  by_contra hKM
  obtain ⟨m, hm, hEC, W', _, _, π, hπ, hker, hrest, hexc⟩ :=
    hR G p B Bs x L D J t n f ψ hctx s1 b L₁ hpair K hK hLK hKM
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
  have hyp := And.intro (ggAutK_hypOne hp hp2 hfusE hE0el hE0card hnorm hKM π hπ hker) hrest
  have hlayer := ggAutK_layer_ne_bot hpair.isComponentOf_inf hLK hpair.le_ggM hH₀C π hker
  have hWle : ggAutKW D K m ≤ Subgroup.centralizer {b} := sup_le hEC hK.1
  have hWne : ggAutKW D K m ≠ ⊤ := fun h =>
    ggStepTwo_centralizer_ne_top hctx.1.2.1 hpair.2.1 (top_le_iff.mp (h ▸ hWle))
  have hKW : CFSG.Open.IsKGroup W' :=
    (CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup hctx.1.2.2.1 _
      hWne).of_surjective π hπ
  rcases hKF W' hKW p _ _ hyp hlayer with htop | hex
  · apply hKM
    have hker' : π.ker ≤ (ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m) :=
      fun w hw => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hker hw))).1
    exact (le_sup_right.trans (ggAutK_le_of_map_eq_top π hker' htop)).trans
      (sup_le hEM inf_le_right)
  · exact hexc hex

theorem ggSixSeventeenFlat_isSubnormal (h314 : GGLemmaThreeFourteenInput)
    (hKF : GGKGroupFusionLayerInputFlat) (hR : GGSixSeventeenAutKFlatInput)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) {b : G} {L₁ : Subgroup G}
    (hpair : GGSixSeventeenPair p B Bs x L D J t f b L₁) :
    IsSubnormal L₁ (Subgroup.centralizer {b}) := by
  have : IsSimpleGroup G := hctx.1.1
  obtain ⟨⟨hBBs, hBsEl, -⟩, ⟨⟨hDB, hDel, hDcard, -⟩, -⟩, -⟩ := hctx.2
  have hDN : D ≤ Subgroup.centralizer {b} := fun d hd => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hBsEl.1
    exact congrArg Subtype.val (mul_comm' (⟨d, hBBs (hDB hd)⟩ : Bs) ⟨b, hpair.1⟩)
  obtain ⟨K, hKc, hLK⟩ := h314 G p hctx.1.2.2.2.2.2.1.1 hctx.1.2.2.2.2.2.1.2.1
    (Subgroup.centralizer {b}) _ D
    (ggStepTwo_kGroup_of_ne_top hctx.1.2.2.1 (ggStepTwo_centralizer_ne_top hctx.1.2.1 hpair.2.1))
    hDel hDcard (s1.2.1.inf_in hDN) L₁ hpair.isComponentOf_inf
  have hKM := ggSixSeventeenComponentFlat_le hKF hR hctx s1 hpair hKc hLK
  exact ggIsSubnormal_trans
    (ggIsSubnormal_of_le_of_le hpair.isComponentOf_inf.2.1 hLK (le_inf hKM hKc.1)) hKc.2.1

theorem ggSixSeventeenFlat_fusion_of_witness (h314 : GGLemmaThreeFourteenInput)
    (hKF : GGKGroupFusionLayerInputFlat) (hR : GGSixSeventeenAutKFlatInput)
    (h610 : GGSixBstarUniqueV2Input) (h611 : GGSixLSixElevenInput)
    (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (hlin : GGSixSeventeenLinearTypeInput)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) {b : G} {L₁ : Subgroup G}
    (hpair : GGSixSeventeenPair p B Bs x L D J t f b L₁) {e : G} (heL : e ∈ L₁) (he1 : e ≠ 1)
    (hfe : GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers e)) :
    GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers b) :=
  ggSixSeventeen_fusion_of_centralizer_le h610 h611 h612 h613t hlin hctx s1 hpair
    (hfe.le_of_isSubnormal (Subgroup.mem_zpowers e) he1 heL hpair.le_ggM
      (ggSixSeventeenFlat_isSubnormal h314 hKF hR hctx s1 hpair))

theorem ggSixSeventeenSixteenFlat_controls (h314 : GGLemmaThreeFourteenInput)
    (hKF : GGKGroupFusionLayerInputFlat) (hR : GGSixSeventeenAutKFlatInput)
    (h610 : GGSixBstarUniqueV2Input) (h611 : GGSixLSixElevenInput)
    (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (hlin : GGSixSeventeenLinearTypeInput)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (s2 : GGSixStepTwo p B Bs x L D J) {e : G}
    (h16 : GGSixSeventeenSixteen p B Bs x L D J t f e) :
    GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers e) := by
  obtain ⟨L₂, L₃, hp₂, hp₃, e', he'R, hd'⟩ := h16
  have hfe' := ggSixSeventeenDirect_controls hctx s1 s2 hd'
  have hc₂ := hp₂.isComponentOf_centralizer
    (ggSixSeventeenFlat_isSubnormal h314 hKF hR hctx s1 hp₂)
  have hc₃ := hp₃.isComponentOf_centralizer
    (ggSixSeventeenFlat_isSubnormal h314 hKF hR hctx s1 hp₃)
  have hCe : Subgroup.centralizer {e} ≤ ggM p B x L D J :=
    hfe'.le_of_isSubnormal (Subgroup.mem_zpowers e') hd'.2.1 he'R
      (sup_le hp₂.le_ggM hp₃.le_ggM) (ggIsSubnormal_sup_components hc₂ hc₃)
  exact ggSixSeventeen_fusion_of_centralizer_le h610 h611 h612 h613t hlin hctx s1 hp₂ hCe

theorem ggSixLemmaSixSeventeenInput_of_inputsFlat (h314 : GGLemmaThreeFourteenInput)
    (hKF : GGKGroupFusionLayerInputFlat) (hR : GGSixSeventeenAutKFlatInput)
    (hW : GGSixSeventeenWitnessInputFor fun _ => True)
    (h610 : GGSixBstarUniqueV2Input) (h611 : GGSixLSixElevenInput)
    (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (hlin : GGSixSeventeenLinearTypeInput) : GGSixLemmaSixSeventeenInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 b hb hb1 L₁ hL₁ hnex
  have hpair : GGSixSeventeenPair p B Bs x L D J t f b L₁ := ⟨hb, hb1, hL₁, hnex⟩
  rcases hW G p B Bs x L D J t n f ψ trivial hctx s1 b L₁ hpair with
    ⟨L₂, hL₂, hcard⟩ | ⟨e, heL, hd | ⟨-, he1, h16⟩⟩
  · exact (s2 b hb hb1 L₂ hL₂ hcard).2
  · exact ggSixSeventeenFlat_fusion_of_witness h314 hKF hR h610 h611 h612 h613t hlin hctx s1
      hpair heL hd.2.1 (ggSixSeventeenDirect_controls hctx s1 s2 hd)
  · exact ggSixSeventeenFlat_fusion_of_witness h314 hKF hR h610 h611 h612 h613t hlin hctx s1
      hpair heL he1
      (ggSixSeventeenSixteenFlat_controls h314 hKF hR h610 h611 h612 h613t hlin hctx s1 s2 h16)

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggSixLemmaSixSeventeenInput_of_schreierFlat (hSch : SchreierFor InCatalog)
    (hKF : GGKGroupFusionLayerInputFlat) (hR : GGSixSeventeenAutKFlatInput)
    (hW : GGSixSeventeenWitnessInputFor fun _ => True)
    (h610 : GGSixBstarUniqueV2Input) (h611 : GGSixLSixElevenInput)
    (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (hlin : GGSixSeventeenLinearTypeInput) : GGSixLemmaSixSeventeenInput :=
  ggSixLemmaSixSeventeenInput_of_inputsFlat (ggLemmaThreeFourteenInput_of_schreier hSch) hKF hR hW
    h610 h611 h612 h613t hlin

end Steps

end CFSG.StandardType

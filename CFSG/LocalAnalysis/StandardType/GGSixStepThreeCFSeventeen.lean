module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFComp
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitness
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSixSeventeenPair (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (f : ℕ) (b : G) (L₁ : Subgroup G) : Prop :=
  b ∈ Bs ∧ b ≠ 1 ∧ IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
    ¬ GGSixSeventeenExcluded p t f L₁

@[expose] def GGSixSeventeenDirect (p : ℕ) (Bs D G₀ : Subgroup G) (e : G) : Prop :=
  e ∈ Bs ∧ e ≠ 1 ∧ ((∃ m ∈ Subgroup.normalizer (Bs : Set G), m⁻¹ * e * m ∈ D) ∨
    ∃ L₂ : Subgroup G, IsComponentOf L₂ (G₀ ⊓ Subgroup.centralizer {e}) ∧
      Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2)

@[expose] def GGSixSeventeenSixteen (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (f : ℕ) (e : G) : Prop :=
  ∃ L₂ L₃ : Subgroup G, GGSixSeventeenPair p B Bs x L D J t f e L₂ ∧
    GGSixSeventeenPair p B Bs x L D J t f e L₃ ∧
    ∃ e' ∈ L₂ ⊔ L₃, GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e'

end Defs

section Pair

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {t : StatedLieTag} {f : ℕ} {b : G} {L₁ : Subgroup G}

namespace GGSixSeventeenPair

theorem isComponentOf_inf (h : GGSixSeventeenPair p B Bs x L D J t f b L₁) :
    IsComponentOf L₁ (ggM p B x L D J ⊓ Subgroup.centralizer {b}) := by
  obtain ⟨-, -, ⟨hle, hsn, hq⟩, -⟩ := h
  have hle' : ggG0 p B x L D J ⊓ Subgroup.centralizer {b} ≤
      ggM p B x L D J ⊓ Subgroup.centralizer {b} :=
    inf_le_inf_right _ Subgroup.le_normalizer
  exact ⟨hle.trans hle', ggIsSubnormal_trans hsn
    (ggIsSubnormal_of_normal hle' (ggStepTwo_inf_normal _ b)), hq⟩

theorem le_ggM (h : GGSixSeventeenPair p B Bs x L D J t f b L₁) : L₁ ≤ ggM p B x L D J :=
  h.isComponentOf_inf.1.trans inf_le_left

theorem le_centralizer (h : GGSixSeventeenPair p B Bs x L D J t f b L₁) :
    L₁ ≤ Subgroup.centralizer {b} :=
  h.2.2.1.1.trans inf_le_right

theorem isComponentOf_centralizer (h : GGSixSeventeenPair p B Bs x L D J t f b L₁)
    (hsn : IsSubnormal L₁ (Subgroup.centralizer {b})) :
    IsComponentOf L₁ (Subgroup.centralizer {b}) :=
  ⟨h.le_centralizer, hsn, h.2.2.1.2.2⟩

end GGSixSeventeenPair

end Pair

section Inputs

@[expose] def GGSixSeventeenAutKInput : Prop :=
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
            GGHypThreeSixteenRest p
              (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map π)
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π) ∧
            ¬ GGFusionException p
              (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map π)
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π)

@[expose] def GGSixSeventeenWitnessInputFor (P : StatedLieTag → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ : Subgroup G), GGSixSeventeenPair p B Bs x L D J t f b L₁ →
        (∃ L₂ : Subgroup G, IsComponentOf L₂ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
          Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2) ∨
        ∃ e ∈ L₁, GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e ∨
          (e ∈ Bs ∧ e ≠ 1 ∧ GGSixSeventeenSixteen p B Bs x L D J t f e)

@[expose] def GGSixSeventeenLinearTypeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → GGSixLinearCase p t n f →
      ∀ (b : G) (L₁ : Subgroup G), GGSixSeventeenPair p B Bs x L D J t f b L₁ → GGTypeAk f L₁

theorem ggSixSeventeenWitnessInput_of_families
    (hlin : GGSixSeventeenWitnessInputFor GGLinearUnitaryTag)
    (hcl : GGSixSeventeenWitnessInputFor GGOtherClassicalTag)
    (hex : GGSixSeventeenWitnessInputFor GGExceptionalTag) :
    GGSixSeventeenWitnessInputFor fun _ => True := by
  intro G _ _ p B Bs x L D J t n f ψ _
  by_cases h₁ : GGLinearUnitaryTag t
  · exact hlin G p B Bs x L D J t n f ψ h₁
  by_cases h₂ : GGOtherClassicalTag t
  · exact hcl G p B Bs x L D J t n f ψ h₂
  exact hex G p B Bs x L D J t n f ψ ⟨h₁, h₂⟩

end Inputs

section Steps

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}

theorem ggSixSeventeenComponent_le (hKF : GGKGroupFusionLayerInput)
    (hR : GGSixSeventeenAutKInput) (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
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
  rcases hKF W' p _ _ hyp hlayer with htop | hex
  · apply hKM
    have hker' : π.ker ≤ (ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m) :=
      fun w hw => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hker hw))).1
    exact (le_sup_right.trans (ggAutK_le_of_map_eq_top π hker' htop)).trans
      (sup_le hEM inf_le_right)
  · exact hexc hex

theorem ggSixSeventeen_isSubnormal (h314 : GGLemmaThreeFourteenInput)
    (hKF : GGKGroupFusionLayerInput) (hR : GGSixSeventeenAutKInput)
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
  have hKM := ggSixSeventeenComponent_le hKF hR hctx s1 hpair hKc hLK
  exact ggIsSubnormal_trans
    (ggIsSubnormal_of_le_of_le hpair.isComponentOf_inf.2.1 hLK (le_inf hKM hKc.1)) hKc.2.1

theorem ggSixSeventeenDirect_controls (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (s2 : GGSixStepTwo p B Bs x L D J) {e : G}
    (he : GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e) :
    GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers e) := by
  obtain ⟨heB, he1, ⟨m, hm, hmD⟩ | ⟨L₂, hL₂, hcard⟩⟩ := he
  · obtain ⟨-, -, -, -, -, -, -, hNBs⟩ := hctx.2
    refine s1.2.1.of_map_conj_le (hNBs hm) ?_
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa [MulAut.conj_apply] using hmD
  · exact (s2 e heB he1 L₂ hL₂ hcard).2

theorem ggSixSeventeen_fusion_of_centralizer_le (h610 : GGSixBstarUniqueV2Input)
    (h611 : GGSixLSixElevenInput) (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (hlin : GGSixSeventeenLinearTypeInput)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) {b : G} {L₁ : Subgroup G}
    (hpair : GGSixSeventeenPair p B Bs x L D J t f b L₁)
    (hC : Subgroup.centralizer {b} ≤ ggM p B x L D J) :
    GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers b) := by
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨-, hBs, -⟩, -, -, -, -, ⟨hBsM, -⟩, -, -⟩ := hctx.2
  have hb : orderOf b = p := orderOf_eq_prime (hBs.2 b hpair.1) hpair.2.1
  refine (ggControlsStrongFusion_zpowers_iff (hb ▸ hp)).mpr ⟨hBsM hpair.1, fun g hg => ?_⟩
  by_contra hgM
  have hZ := s1.1
  have hU := h610 G p B Bs x L D J t n f ψ hctx hZ
  rcases h611 G p B Bs x L D J t n f ψ hctx hZ hU b hpair.1 hC g hg hgM with hl | ht
  · exact (h612 G p B Bs x L D J t n f ψ hctx hZ hU b hpair.1 hC g hg hgM hl).2 L₁ hpair.2.2.1
      (hlin G p B Bs x L D J t n f ψ hctx hZ hl b L₁ hpair)
  · exact hgM (h613t G p B Bs x L D J t n f ψ hctx hZ hU
      (fun d hd hd1 => s1.2.1.centralizer_le hd hd1) b hpair.1 hC g hg ht)

theorem ggSixSeventeen_fusion_of_witness (h314 : GGLemmaThreeFourteenInput)
    (hKF : GGKGroupFusionLayerInput) (hR : GGSixSeventeenAutKInput)
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
      (ggSixSeventeen_isSubnormal h314 hKF hR hctx s1 hpair))

theorem ggSixSeventeenSixteen_controls (h314 : GGLemmaThreeFourteenInput)
    (hKF : GGKGroupFusionLayerInput) (hR : GGSixSeventeenAutKInput)
    (h610 : GGSixBstarUniqueV2Input) (h611 : GGSixLSixElevenInput)
    (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (hlin : GGSixSeventeenLinearTypeInput)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (s2 : GGSixStepTwo p B Bs x L D J) {e : G}
    (h16 : GGSixSeventeenSixteen p B Bs x L D J t f e) :
    GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers e) := by
  obtain ⟨L₂, L₃, hp₂, hp₃, e', he'R, hd'⟩ := h16
  have hfe' := ggSixSeventeenDirect_controls hctx s1 s2 hd'
  have hc₂ := hp₂.isComponentOf_centralizer (ggSixSeventeen_isSubnormal h314 hKF hR hctx s1 hp₂)
  have hc₃ := hp₃.isComponentOf_centralizer (ggSixSeventeen_isSubnormal h314 hKF hR hctx s1 hp₃)
  have hCe : Subgroup.centralizer {e} ≤ ggM p B x L D J :=
    hfe'.le_of_isSubnormal (Subgroup.mem_zpowers e') hd'.2.1 he'R
      (sup_le hp₂.le_ggM hp₃.le_ggM) (ggIsSubnormal_sup_components hc₂ hc₃)
  exact ggSixSeventeen_fusion_of_centralizer_le h610 h611 h612 h613t hlin hctx s1 hp₂ hCe

theorem ggSixLemmaSixSeventeenInput_of_inputs (h314 : GGLemmaThreeFourteenInput)
    (hKF : GGKGroupFusionLayerInput) (hR : GGSixSeventeenAutKInput)
    (hW : GGSixSeventeenWitnessInputFor fun _ => True)
    (h610 : GGSixBstarUniqueV2Input) (h611 : GGSixLSixElevenInput)
    (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (hlin : GGSixSeventeenLinearTypeInput) : GGSixLemmaSixSeventeenInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 b hb hb1 L₁ hL₁ hnex
  have hpair : GGSixSeventeenPair p B Bs x L D J t f b L₁ := ⟨hb, hb1, hL₁, hnex⟩
  rcases hW G p B Bs x L D J t n f ψ trivial hctx s1 b L₁ hpair with
    ⟨L₂, hL₂, hcard⟩ | ⟨e, heL, hd | ⟨-, he1, h16⟩⟩
  · exact (s2 b hb hb1 L₂ hL₂ hcard).2
  · exact ggSixSeventeen_fusion_of_witness h314 hKF hR h610 h611 h612 h613t hlin hctx s1 hpair
      heL hd.2.1 (ggSixSeventeenDirect_controls hctx s1 s2 hd)
  · exact ggSixSeventeen_fusion_of_witness h314 hKF hR h610 h611 h612 h613t hlin hctx s1 hpair
      heL he1
      (ggSixSeventeenSixteen_controls h314 hKF hR h610 h611 h612 h613t hlin hctx s1 s2 h16)

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggSixLemmaSixSeventeenInput_of_schreier (hSch : SchreierFor InCatalog)
    (hKF : GGKGroupFusionLayerInput) (hR : GGSixSeventeenAutKInput)
    (hW : GGSixSeventeenWitnessInputFor fun _ => True)
    (h610 : GGSixBstarUniqueV2Input) (h611 : GGSixLSixElevenInput)
    (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (hlin : GGSixSeventeenLinearTypeInput) : GGSixLemmaSixSeventeenInput :=
  ggSixLemmaSixSeventeenInput_of_inputs (ggLemmaThreeFourteenInput_of_schreier hSch) hKF hR hW
    h610 h611 h612 h613t hlin

end Steps

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagNbr
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSchreier
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompCentre
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompNormal
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompKd
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompCentJ

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section General

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_sup_centralizer (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((K ⊔ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
  have hmap : ∀ n ∈ Subgroup.normalizer (K : Set G), ∀ h ∈ K ⊔ Subgroup.centralizer (K : Set G),
      n * h * n⁻¹ ∈ K ⊔ Subgroup.centralizer (K : Set G) := by
    intro n hn h hh
    have hle : K ⊔ Subgroup.centralizer (K : Set G) ≤
        (K ⊔ Subgroup.centralizer (K : Set G)).comap (MulAut.conj n).toMonoidHom := by
      refine sup_le (fun k hk => ?_) (fun c hc => ?_) <;>
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hn k).mp hk)
      · exact Subgroup.mem_sup_right (ggConj_mem_centralizer_of_mem_normalizer hn hc)
    have := hle hh
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hmap n hn h hh, fun hh => ?_⟩
  have := hmap n⁻¹ (inv_mem hn) _ hh
  have e : n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem GGInnerDiagOn.mono {S S' K : Subgroup G} (h : GGInnerDiagOn S K) (hS'S : S' ≤ S) :
    GGInnerDiagOn S' K :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hS'S.trans hP.1, fun b hb => hP.2 b (hS'S hb)⟩) h

end General

section DForm

@[expose] def GGSixInndiagNormalDInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) →
    Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J →
      ∀ d ∈ D, d ≠ 1 → Subgroup.normalizer (ggKd p B x L D J d : Set G) ≤
        Subgroup.normalizer ((D ⊔ ggKd p B x L D J d ⊔
          Subgroup.centralizer (ggKd p B x L D J d : Set G) : Subgroup G) : Set G)

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.normalizer_ggKd_le_of_d (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ)
    (h69 : ∀ g : G, J.map (MulAut.conj g).toMonoidHom ≤ ggM p B x L D J →
      D.map (MulAut.conj g).toMonoidHom ≤ ggM p B x L D J → g ∈ ggM p B x L D J)
    (h66 : Subgroup.centralizer (J : Set G) ≤ ggM p B x L D J) {d : G} (hd : d ∈ D)
    (hX : Subgroup.normalizer (ggKd p B x L D J d : Set G) ≤
      Subgroup.normalizer ((D ⊔ ggKd p B x L D J d ⊔
        Subgroup.centralizer (ggKd p B x L D J d : Set G) : Subgroup G) : Set G)) :
    Subgroup.normalizer (ggKd p B x L D J d : Set G) ≤ ggM p B x L D J := by
  have hKM := h.ggKd_sup_centralizer_le h66 hd
  refine normalizer_le_of_conj_le h69 ((le_ggKd p B x L D J d).trans
    (le_sup_right.trans le_sup_left)) (le_sup_left.trans le_sup_left) ?_ hX
  exact sup_le (sup_le h.d_le_ggM (le_sup_left.trans hKM)) (le_sup_right.trans hKM)

end DForm

section DProof

theorem ggSixInndiagNormalDInput_of_prime (hN : GGInndiagNormalInput)
    (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input) (hc₂ : GGCor42Input)
    (hpJ : GGStdSubPrimeInput) : GGSixInndiagNormalDInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx h65 _ d hd hd1
  have hcfg := hctx.config
  have hAll := hc₂ G p B Bs x L D J hcfg (hc₁ G p B Bs x L D J hcfg (hc₀ G p B Bs x L D J hcfg))
  have hO : ∀ lab, LargeEvenInLambda2 lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I) :=
    fun _ hlab => largeEvenLabelAll_outdiag_simple hlab
  by_cases hdx : d ∈ Subgroup.zpowers x
  · rw [hctx.ggKd_eq_of_mem_zpowers hdx hd1]
    exact normalizer_le_normalizer_sup_of_innerDiagOn hO hN (hAll.1.mono hctx.d_le_bstar)
  · by_cases hDK : D ≤ Subgroup.centralizer (ggKd p B x L D J d : Set G)
    · have he : D ⊔ ggKd p B x L D J d ⊔ Subgroup.centralizer (ggKd p B x L D J d : Set G) =
          ggKd p B x L D J d ⊔ Subgroup.centralizer (ggKd p B x L D J d : Set G) := by
        rw [sup_comm D, sup_assoc, sup_eq_right.mpr hDK]
      rw [he]
      exact normalizer_le_normalizer_sup_centralizer _
    · exact normalizer_le_normalizer_sup_of_innerDiagOn hO hN
        ((hAll.2 d _ (ggSixKdNbrInput_of_prime hpJ G p B Bs x L D J t n f ψ hctx h65 d hd hdx
          hDK)).mono hctx.d_le_bstar)

end DProof

section Step

theorem ggSixStepOneV2Input_of_lemmas_d (ha₀ : GGLNoncyclicInput)
    (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input) (hc₂ : GGCor42Input)
    (hc₃ : GGNoTransvectionInput) (hnbr : GGSixNbrCentralizerInput)
    (h63 : GGSixCentralizerOddInput) (h64 : GGSixCentreOddInput) (h65 : GGSixKdComponentInput)
    (h66 : GGSixCentralizerJInput) (h68 : GGSixComponentsNormalInput)
    (h68i : GGSixInnerOnKdInput) (h69 : GGSixInndiagNormalDInput) (hS : GGSchreierPerfectInput)
    (hT : GGTwoSignalizerGenInput) (h610 : GGSixBstarUniqueV2Input)
    (h611 : GGSixLSixElevenInput) (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (h613d : GGSixLinearJInput) : GGSixStepOneV2Input := by
  intro G _ _ p B Bs x L D J t n f ψ hctx
  have hp := hctx.prime
  have hC2 : Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J :=
    centralizer_le_ggM_of_nbr hctx.sstar (ha₀ G p B x L hctx.thmI) hctx.stdSub.1
      (hnbr G p B x L D J hctx.thmI hctx.stdSub)
  have hodd := h63 G p B Bs x L D J t n f ψ hctx
    (not_dvd_card_centralizer_ggG0_of_stdSub hp hctx.sstar hctx.stdType hctx.stdSub)
  obtain ⟨hZJ, hZK⟩ := h64 G p B Bs x L D J t n f ψ hctx hodd
  have hcomp := h65 G p B Bs x L D J t n f ψ hctx hodd hZJ hZK
  have hCJ := h66 G p B Bs x L D J t n f ψ hctx hC2 hodd hcomp
  have hnorm := h68 G p B Bs x L D J t n f ψ hctx hC2 hodd hcomp
  have hsig := hctx.signalizer_le hC2 hcomp hCJ hnorm
    (h68i G p B Bs x L D J t n f ψ hctx hcomp hCJ hnorm)
  have h9i : ∀ g : G, J.map (MulAut.conj g).toMonoidHom ≤ ggM p B x L D J →
      D.map (MulAut.conj g).toMonoidHom ≤ ggM p B x L D J → g ∈ ggM p B x L D J :=
    fun g hJg hDg => hctx.mem_of_conj_le hS hT hodd hsig hJg hDg
  have h9ii : ∀ d ∈ D, d ≠ 1 →
      Subgroup.normalizer (ggKd p B x L D J d : Set G) ≤ ggM p B x L D J :=
    fun d hd hd1 => hctx.normalizer_ggKd_le_of_d h9i hCJ hd
      (h69 G p B Bs x L D J t n f ψ hctx hcomp hCJ d hd hd1)
  have h9iii : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J :=
    fun d hd hd1 => hctx.centralizer_le_ggM h9i hd (hcomp d hd hd1) (hnorm d hd hd1)
      (h9ii d hd hd1)
  have hC : Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ :=
    centralizer_eq_bot_of_signalizers hctx.charTwo hp hctx.ne_two hctx.le_ggG0
      hctx.le_centralizer_J hodd hsig hctx.two_dvd_card_j
  have hU := h610 G p B Bs x L D J t n f ψ hctx hC
  have hcfg := hctx.config
  have hOp := hc₁ G p B Bs x L D J hcfg (hc₀ G p B Bs x L D J hcfg)
  have hNoTr := hc₃ G p B Bs x L D J hcfg hOp (hc₂ G p B Bs x L D J hcfg hOp)
  refine ⟨hC, ?_, hsig, exists_sylow_of_bstarUnique hp hctx.bstar.2.1 hctx.bstar_le_normalizer hU,
    not_ggTransvection_of_noTransvection hp hctx.bstar.2.1 hNoTr⟩
  rw [ggControlsStrongFusion_iff]
  exact ⟨hctx.d_le_ggM, fun e he he1 g hg =>
    hctx.mem_of_conj_mem_d h611 h612 h613t h613d hC hU h9iii he he1 hg⟩

end Step

section Outdiag

theorem ggSixStepOneV2Input_of_lemmas_outdiag (ha₀ : GGLNoncyclicInput)
    (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input) (hc₂ : GGCor42Input)
    (hc₃ : GGNoTransvectionInput) (hnbr : GGSixNbrCentralizerInput)
    (h63 : GGSixCentralizerOddInput) (h64 : GGSixCentreOddInput) (h65 : GGSixKdComponentInput)
    (h66 : GGSixCentralizerJInput) (h68 : GGSixComponentsNormalInput)
    (hN : GGInndiagNormalInput) (hpJ : GGStdSubPrimeInput) (hS : GGSchreierPerfectInput)
    (hT : GGTwoSignalizerGenInput) (h610 : GGSixBstarUniqueV2Input)
    (h611 : GGSixLSixElevenInput) (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput)
    (h613d : GGSixLinearJInput) : GGSixStepOneV2Input :=
  ggSixStepOneV2Input_of_lemmas_d ha₀ hc₀ hc₁ hc₂ hc₃ hnbr h63 h64 h65 h66 h68
    (ggSixInnerOnKdInput_of_prime hN hc₀ hc₁ hc₂ hpJ)
    (ggSixInndiagNormalDInput_of_prime hN hc₀ hc₁ hc₂ hpJ) hS hT h610 h611 h612 h613t h613d

end Outdiag

end CFSG.StandardType

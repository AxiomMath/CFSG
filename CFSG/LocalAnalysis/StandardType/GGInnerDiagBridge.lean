module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inner

variable {U : Type*} [Group U] {G : Type*} [Group G]

theorem ggPsiInnerDiag_of_induces_conj (Δ : UniversalRootDatum U) (ψ : U →* G)
    (hperf : commutator ↥ψ.range = ⊤) {R : Type} [Group R]
    (θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* R) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G)) {r : R}
    (h : LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) (MulAut.conj r)) :
    GGPsiInnerDiag Δ ψ c := by
  obtain ⟨y, hy⟩ := θ.surjective r
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hmem : ∀ l : ↥ψ.range, c⁻¹ * (l : G) * c ∈ ψ.range := fun l => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hc) l).mp l.2
    rwa [inv_inv] at this
  let α : ↥ψ.range →* ↥ψ.range :=
    { toFun := fun l => ⟨c⁻¹ * (l : G) * c, hmem l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hα : ∀ l, ((α l : ↥ψ.range) : G) = c⁻¹ * (l : G) * c := fun _ => rfl
  have hβα : (MulAut.conj g₀).toMonoidHom = α := by
    refine TypeA.eq_of_inv_mul_mem_center hperf _ _ fun l => ?_
    have hl := h l (α l) (hα l).symm
    rw [MulAut.conj_apply, ← hy, ← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hl
    exact QuotientGroup.eq.mp (θ.injective hl)
  have key : ∀ z : U, (g₀ : G) * ψ z * (g₀ : G)⁻¹ = c⁻¹ * ψ z * c := fun z => by
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hβα (⟨ψ z, z, rfl⟩ : ↥ψ.range))
    rw [hα] at h1
    exact h1
  refine ⟨g₀, g₀.2, fun γ _ => ⟨1, Subgroup.one_mem _, fun z _ => ?_⟩⟩
  rw [one_mul, inv_one, mul_one]
  calc (c * (g₀ : G))⁻¹ * ψ z * (c * g₀) = (g₀ : G)⁻¹ * (c⁻¹ * ψ z * c) * g₀ := by group
    _ = (g₀ : G)⁻¹ * ((g₀ : G) * ψ z * (g₀ : G)⁻¹) * g₀ := by rw [key z]
    _ = ψ z := by group

theorem ggPsiInnerDiag_of_induces_mem_inn (Δ : UniversalRootDatum U) (ψ : U →* G)
    (hperf : commutator ↥ψ.range = ⊤) {R : Type} [Group R]
    (θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* R) {I : Set (MulAut R)}
    (hI : I ⊆ LargeEvenInnSet R) {c : G} (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (h : ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) :
    GGPsiInnerDiag Δ ψ c := by
  obtain ⟨φ, hφ, hind⟩ := h
  obtain ⟨r, rfl⟩ := hI hφ
  exact ggPsiInnerDiag_of_induces_conj Δ ψ hperf θ hc hind

end Inner

@[expose] def GGInnerDiagOpenTag (t : StatedLieTag) : Prop :=
  t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨
    t = .E8 ∨ t = .twistedE6

section Genuine

@[expose] def GGInnerDiagMarkingAt (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G) (G₀ : Subgroup G),
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
      LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ c ∈ Subgroup.normalizer (G₀ : Set G),
        GGPsiInnerDiag (ggU t n f).D ψ c →
          ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ)

@[expose] def GGInnerDiagMarkingInput : Prop :=
  ∀ t : StatedLieTag, GGInnerDiagMarkingAt t

theorem ggInnerDiagMarkingAt_of_rank {t : StatedLieTag} (h : ∀ n f, (ggU t n f).D.rank < 2) :
    GGInnerDiagMarkingAt t := by
  intro G _ _ n f ψ G₀ hpres
  exact absurd hpres.1.2 (by have := h n f; omega)

theorem ggInnerDiagMarkingAt_POmegaOdd : GGInnerDiagMarkingAt .POmegaOdd := by
  intro G _ _ n f ψ G₀ hpres
  exact absurd rfl hpres.1.1.2.2.2

theorem ggInnerDiagMarkingInput_of_open (hA : GGInnerDiagMarkingAt .PSL)
    (h : ∀ t, GGInnerDiagOpenTag t → GGInnerDiagMarkingAt t) : GGInnerDiagMarkingInput := by
  have h0 : ∀ t, (∀ n f, (ggU t n f).D.rank = 0) → GGInnerDiagMarkingAt t := fun t ht =>
    ggInnerDiagMarkingAt_of_rank fun n f => by rw [ht n f]; omega
  intro t
  cases t
  · exact hA
  · exact h _ (.inl rfl)
  · exact h _ (.inr (.inl rfl))
  · exact ggInnerDiagMarkingAt_POmegaOdd
  · exact h _ (.inr (.inr (.inl rfl)))
  · exact h _ (.inr (.inr (.inr (.inl rfl))))
  · exact h0 _ fun _ _ => rfl
  · exact h _ (.inr (.inr (.inr (.inr (.inl rfl)))))
  · exact h _ (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  · exact h _ (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))))
  · exact h _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))))
  · exact h _ (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))))
  · exact h0 _ fun _ _ => rfl
  · exact h0 _ fun _ _ => rfl
  · exact h0 _ fun _ _ => rfl
  · exact h0 _ fun _ _ => rfl
  · exact h0 _ fun _ _ => rfl

variable {G : Type} [Group G] [Finite G]

theorem ggInnerDiagOn_of_presents_mk (hR : GGInnerDiagMarkingInput) {G₀ Bs : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ)
    (hBsN : Bs ≤ Subgroup.normalizer (G₀ : Set G))
    (hVI : ∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) : GGInnerDiagOn Bs G₀ :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hBsN, fun b hb => hP b (hBsN hb) (hVI b hb)⟩)
    (hR t G n f ψ G₀ hpres)

theorem ggSecOneFiveV2Input_of_inputs_mk (ha : GGBstarInput) (ha₀ : GGLNoncyclicInput)
    (hb : GGStdSubPreInput) (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input)
    (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput) (hd : GGCoxeterLabelInput)
    (he : GGPropFiveTwentyOneV2Input) (hf : GGHypSixV2Input) (hg₁ : GGCorFiveTwentyInput)
    (hg₂ : GGOmegaOneInput) (hR : GGInnerDiagMarkingInput) : GGSecOneFiveV2Input := by
  intro G _ _ _ hnonab hK hchar he4 p hp B x L hS hst
  have hI : GGThmIHyp p B x L := ⟨inferInstance, hnonab, hK, hchar, he4, hp, hS, hst⟩
  obtain ⟨Bs, hBs⟩ := ha G p B x L hI
  obtain ⟨D, J, hDJ⟩ := exists_stdSub_of_stdSubPre (hb G p B x L hI)
  have hcfg : GGConfig p B Bs x L D J := ⟨hI, hBs, hDJ⟩
  have hOp := hc₁ G p B Bs x L D J hcfg (hc₀ G p B Bs x L D J hcfg)
  have hInn := hc₂ G p B Bs x L D J hcfg hOp
  have hNoTr := hc₃ G p B Bs x L D J hcfg hOp hInn
  have hW := hd G p B Bs x L D J hcfg hOp hInn hNoTr
  obtain ⟨t, n, f, ψ, hpres⟩ := he G p B Bs x L D J hcfg hOp hInn hNoTr hW
  have hnc := ha₀ G p B x L hI
  have hBsN := bstar_le_normalizer_ggG0 hS hnc hDJ.1 hBs
  have hVI := hf G p B Bs x L D J hcfg hOp hInn t n f ψ hpres hBsN
  have hNBs := hg₁ G p B Bs x L D J hcfg hOp hInn hNoTr
    (ggInnerDiagOn_of_presents_mk hR hpres hBsN hVI)
  have hCB := centralizer_le_normalizer_ggG0 hS hnc hDJ.1
  have hNB := normalizer_le_of_frattini hp.1 hBs (hg₂ G p B Bs x L D J hcfg hOp hInn) hCB hNBs
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, hperf, hmodel⟩ := hpres
  exact ⟨Bs, D, J, t, n, f, ψ, hBs, hDJ, ⟨hadm, hrk⟩, ⟨hrange, hker⟩, ⟨hperf, hmodel⟩,
    ⟨hBsN, hVI⟩, hNB, hNBs⟩

end Genuine

section Bridge

theorem ggInnerDiagMarkingInput_of_bridge (hR : GGInnerDiagBridgeInput) :
    GGInnerDiagMarkingInput := by
  intro t G _ _ n f ψ G₀ hpres
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, hperf, hmodel⟩ := hpres
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ hP c hc hd => (hP.2 c hc).mpr hd)
    (hR G t n f ψ hadm hrk hker G₀ hrange _
      (ggLieModelMarkingInput_holds _ t n f hadm hperf hmodel))

end Bridge

section Assembly

theorem lc_gl_std_of_v2_steps_mk (hHolt : HoltUniqueFixedPointSimple) (ha : GGBstarInput)
    (ha₀ : GGLNoncyclicInput) (hb : GGStdSubPreInput) (hc₀ : GGFieldNbrCanonicalInput)
    (hc₁ : GGProp41Input) (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput)
    (hd : GGCoxeterLabelInput) (he : GGPropFiveTwentyOneV2Input) (hf : GGHypSixV2Input)
    (hg₁ : GGCorFiveTwentyInput) (hg₂ : GGOmegaOneInput) (hR : GGInnerDiagMarkingInput)
    (h1 : GGSixStepOneV2Input) (h2 : GGSixStepTwoV2Input) (h3a : GGSixStepThreeAInput)
    (h3b : GGSixStepThreeBInput) (h3c : GGSixStepThreeCInput) (h3d : GGSixStepThreeDInput)
    (hKG : GGRootInvolutionCentralInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he4 : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G :=
  lc_gl_std_of_v2_inputs hHolt
    (ggSecOneFiveV2Input_of_inputs_mk ha ha₀ hb hc₀ hc₁ hc₂ hc₃ hd he hf hg₁ hg₂ hR)
    (ggSecSixV2Input_of_inputs h1 h2 h3a h3b h3c h3d hKG)
    G hnonab hK hchar he4 p hp B x L hS hst

end Assembly

end CFSG.StandardType

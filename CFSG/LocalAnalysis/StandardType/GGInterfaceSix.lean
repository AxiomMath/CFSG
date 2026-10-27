module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceBridge
public import CFSG.LocalAnalysis.StandardType.GGSix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Defs

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U]

@[expose] def GGSixCtxV2 (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (Δ : UniversalRootDatum U) (t : StatedLieTag) (n f : ℕ) (ψ : U →* G) : Prop :=
  GGThmIHyp p B x L ∧ GGSixHypV2Core p B Bs x L D J Δ t n f ψ

@[expose] def GGStepThreeChoice (p : ℕ) (Bs M : Subgroup G) (Δ : UniversalRootDatum U)
    (t : StatedLieTag) (ψ : U →* G) (E : Subgroup G) (r : G) : Prop :=
  E ≤ Bs ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ GGControlsStrongFusion M E ∧
    orderOf r = 2 ∧ ∃ γ, GGRootClass Δ t γ ∧ ∃ u : U,
      E ≤ Subgroup.centralizer (ggRootSub Δ ψ γ u : Set G) ∧ r ∈ ggRootSub Δ ψ γ u

end Defs

section Elementary

variable {G : Type} [Group G] {U : Type} [Group U] {Δ : UniversalRootDatum U}

theorem ggRootSub_le_range (ψ : U →* G) (γ : Fin Δ.rank → ℤ) (u : U) :
    ggRootSub Δ ψ γ u ≤ ψ.range := by
  rintro _ ⟨z, -, rfl⟩
  exact ⟨z, rfl⟩

theorem GGStepThreeChoice.rootInvolution {p : ℕ} {Bs M : Subgroup G} {t : StatedLieTag}
    {ψ : U →* G} {E : Subgroup G} {r : G} (h : GGStepThreeChoice p Bs M Δ t ψ E r) :
    GGRootInvolution Δ t ψ r := by
  obtain ⟨-, -, -, -, hr, γ, hγ, u, -, hru⟩ := h
  exact ⟨hr, γ, hγ, u, hru⟩

theorem GGStepThreeChoice.mem_range {p : ℕ} {Bs M : Subgroup G} {t : StatedLieTag}
    {ψ : U →* G} {E : Subgroup G} {r : G} (h : GGStepThreeChoice p Bs M Δ t ψ E r) :
    r ∈ ψ.range := by
  obtain ⟨-, -, -, -, -, γ, -, u, -, hru⟩ := h
  exact ggRootSub_le_range ψ γ u hru

theorem conj_mem_ggRootSub {ψ : U →* G} {γ : Fin Δ.rank → ℤ} {u : U} {r : G}
    (hr : r ∈ ggRootSub Δ ψ γ u) (v : U) :
    ψ v * r * (ψ v)⁻¹ ∈ ggRootSub Δ ψ γ (v * u) := by
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hr
  refine ⟨_, ⟨z, hz, rfl⟩, ?_⟩
  change ψ (v * u * z * (v * u)⁻¹) = ψ v * ψ (u * z * u⁻¹) * (ψ v)⁻¹
  simp only [map_mul, map_inv, mul_inv_rev]
  group

theorem GGRootInvolution.conj {t : StatedLieTag} {ψ : U →* G} {r : G}
    (h : GGRootInvolution Δ t ψ r) (v : U) : GGRootInvolution Δ t ψ (ψ v * r * (ψ v)⁻¹) := by
  obtain ⟨hr, γ, hγ, u, hru⟩ := h
  refine ⟨?_, γ, hγ, v * u, conj_mem_ggRootSub hru v⟩
  have ho := MulEquiv.orderOf_eq (MulAut.conj (ψ v)) r
  rw [MulAut.conj_apply] at ho
  rw [ho, hr]

theorem centralizer_conj_le {M : Subgroup G} {r m : G} (hC : Subgroup.centralizer {r} ≤ M)
    (hm : m ∈ M) : Subgroup.centralizer {m * r * m⁻¹} ≤ M := by
  intro g hg
  have hg' : m⁻¹ * g * m ∈ Subgroup.centralizer {r} := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    have := congrArg (fun y => m⁻¹ * y * m) hg
    simp only [mul_assoc, inv_mul_cancel_left] at this ⊢
    calc m⁻¹ * (g * (m * r)) = m⁻¹ * (g * (m * (r * (m⁻¹ * m)))) := by group
      _ = m⁻¹ * (m * (r * (m⁻¹ * (g * m)))) := by
          rw [show g * (m * (r * (m⁻¹ * m))) = g * (m * r * m⁻¹) * m by group, hg]; group
      _ = r * (m⁻¹ * (g * m)) := by group
  have h1 := hC hg'
  have := M.mul_mem (M.mul_mem hm h1) (M.inv_mem hm)
  simpa [mul_assoc] using this

end Elementary

section Inputs

@[expose] def GGSixStepOneV2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J

@[expose] def GGSixStepTwoV2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J

@[expose] def GGSixStepThreeAInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J →
      ∃ (E : Subgroup G) (r : G), GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r

@[expose] def GGSixStepThreeBInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J

@[expose] def GGSixStepThreeCInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
          Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J))

@[expose] def GGSixStepThreeDInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        Subgroup.centralizer {r} ≤ ggM p B x L D J →
        Odd ((ggG0 p B x L D J).relIndex (ggM p B x L D J)) →
          GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers r)

@[expose] def GGRootInvolutionCentralInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → ψ.ker ≤ Subgroup.center (ggU t n f).K →
    ∀ G₀ : Subgroup G, ψ.range = G₀ → ∀ r : G, GGRootInvolution (ggU t n f).D t ψ r →
      ∃ T : Sylow 2 G₀, r ∈ (T : Subgroup G₀).map G₀.subtype ∧
        (T : Subgroup G₀).map G₀.subtype ≤ Subgroup.centralizer {r}

@[expose] def GGMarkedPresentedInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSixCtx p B Bs x L D J → GGSixStepOne p B Bs x L D J →
      ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGSixHypV2Core p B Bs x L D J (ggU t n f).D t n f ψ

theorem ggSixStepThree_of_split (h3a : GGSixStepThreeAInput) (h3b : GGSixStepThreeBInput)
    (h3c : GGSixStepThreeCInput) (h3d : GGSixStepThreeDInput)
    (hKG : GGRootInvolutionCentralInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (s2 : GGSixStepTwo p B Bs x L D J) :
    GGSixStepThree p B x L D J := by
  obtain ⟨E, r, hch⟩ := h3a G p B Bs x L D J t n f ψ hctx s1 s2
  have hC := h3b G p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  have hodd := h3c G p B Bs x L D J t n f ψ hctx s1 s2 E r hch hC
  have hfus := h3d G p B Bs x L D J t n f ψ hctx s1 s2 E r hch hC hodd
  obtain ⟨-, -, -, ⟨hadm, -⟩, ⟨hrange, hker⟩, -⟩ := hctx
  obtain ⟨T, hrT, hTc⟩ := hKG G t n f ψ hadm hker _ hrange r hch.rootInvolution
  exact ⟨hodd, r, Subgroup.map_subtype_le _ hrT, hch.2.2.2.2.1, ⟨T, hrT, hTc⟩, hC, hfus⟩

theorem ggSecSixV2Input_of_inputs (h1 : GGSixStepOneV2Input) (h2 : GGSixStepTwoV2Input)
    (h3a : GGSixStepThreeAInput) (h3b : GGSixStepThreeBInput) (h3c : GGSixStepThreeCInput)
    (h3d : GGSixStepThreeDInput) (hKG : GGRootInvolutionCentralInput) : GGSecSixV2Input := by
  intro G _ _ _ hnonab hK hchar he p hp B x L hS hst Bs D J t n f ψ hsix
  have hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ :=
    ⟨⟨inferInstance, hnonab, hK, hchar, he, hp, hS, hst⟩, hsix⟩
  have s1 := h1 G p B Bs x L D J t n f ψ hctx
  exact ggSix_holt_of_stepThree (ggSixStepThree_of_split h3a h3b h3c h3d hKG hctx s1
    (h2 G p B Bs x L D J t n f ψ hctx s1))

theorem ggSixCtx_of_v2 (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput)
    (ha' : GGBstarRankInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) : GGSixCtx p B Bs x L D J := by
  obtain ⟨hI, hsix⟩ := hctx
  obtain ⟨hs, hnonab, hK, hchar, he, hp, hS, hst⟩ := hI
  exact ⟨hs, hnonab, hK, hchar, he, hp, hS, hst,
    ggSixHyp_of_v2Core hR1 hR ha' ⟨hs, hnonab, hK, hchar, he, hp, hS, hst⟩ hsix⟩

theorem ggSixStepOneV2Input_of_input (h1 : GGSixStepOneInput) (hR1 : GGLieModelMarkingInput)
    (hR : GGInnerDiagBridgeInput) (ha' : GGBstarRankInput) : GGSixStepOneV2Input :=
  fun G _ _ p B Bs x L D J _ _ _ _ hctx =>
    h1 G p B Bs x L D J (ggSixCtx_of_v2 hR1 hR ha' hctx)

theorem ggSixStepTwoV2Input_of_input (h2 : GGSixStepTwoInput) (hR1 : GGLieModelMarkingInput)
    (hR : GGInnerDiagBridgeInput) (ha' : GGBstarRankInput) : GGSixStepTwoV2Input :=
  fun G _ _ p B Bs x L D J _ _ _ _ hctx s1 =>
    h2 G p B Bs x L D J (ggSixCtx_of_v2 hR1 hR ha' hctx) s1

theorem ggSixStepThreeInput_of_split (hfw : GGMarkedPresentedInput) (h3a : GGSixStepThreeAInput)
    (h3b : GGSixStepThreeBInput) (h3c : GGSixStepThreeCInput) (h3d : GGSixStepThreeDInput)
    (hKG : GGRootInvolutionCentralInput) : GGSixStepThreeInput := by
  intro G _ _ p B Bs x L D J hctx s1 s2
  obtain ⟨t, n, f, ψ, hsix⟩ := hfw G p B Bs x L D J hctx s1
  obtain ⟨hs, hnonab, hK, hchar, he, hp, hS, hst, -⟩ := hctx
  exact ggSixStepThree_of_split h3a h3b h3c h3d hKG
    ⟨⟨hs, hnonab, hK, hchar, he, hp, hS, hst⟩, hsix⟩ s1 s2

end Inputs

end CFSG.StandardType

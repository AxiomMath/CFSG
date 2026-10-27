module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceSix
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

theorem GGStepThreeChoice.le_centralizer {G : Type} [Group G] {U : Type} [Group U]
    {Δ : UniversalRootDatum U} {p : ℕ} {Bs M : Subgroup G} {t : StatedLieTag} {ψ : U →* G}
    {E : Subgroup G} {r : G} (h : GGStepThreeChoice p Bs M Δ t ψ E r) :
    E ≤ Subgroup.centralizer {r} := by
  obtain ⟨-, -, -, -, -, γ, -, u, hEX, hrX⟩ := h
  intro e he
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((Subgroup.mem_centralizer_iff.mp (hEX he)) r hrX).symm

section Inputs

@[expose] def GGRootPlaneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∃ (E : Subgroup G) (γ : Fin (ggU t n f).D.rank → ℤ) (u : (ggU t n f).K) (r : G),
        E ≤ Bs ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ GGRootClass (ggU t n f).D t γ ∧
        E ≤ Subgroup.centralizer (ggRootSub (ggU t n f).D ψ γ u : Set G) ∧
        r ∈ ggRootSub (ggU t n f).D ψ γ u ∧ orderOf r = 2 ∧
        ∀ e ∈ E, e ≠ 1 → e ∈ D ∨ ∃ L₁ : Subgroup G,
          IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {e}) ∧
            Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2

@[expose] def GGRootCentralizerCyclicInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    ∀ r : G, GGRootInvolution (ggU t n f).D t ψ r →
    ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (ψ.range : Set G) ⊓ Subgroup.centralizer {r} →
      (∀ y ∈ Y, GGPsiInnerDiag (ggU t n f).D ψ y) →
        ∃ y₀ ∈ Y, Y ≤ Subgroup.zpowers y₀ ⊔ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {r})

@[expose] def GGSixRootCentralizerSubnormalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        ∃ X : Subgroup G, X ≤ ggM p B x L D J ∧ IsSubnormal X (Subgroup.centralizer {r}) ∧
          ∀ y ∈ ggOTwoPrime (ggG0 p B x L D J ⊓ Subgroup.centralizer {r}), y ^ p = 1 → y ∈ X

@[expose] def GGSixRootCentralizerQuotientInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J → ∀ (E : Subgroup G) (r : G),
      GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r →
        ∃ X : Subgroup (↥(Subgroup.centralizer {r}) ⧸
            CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r})),
          X ≤ ((ggM p B x L D J).subgroupOf (Subgroup.centralizer {r})).map
            (QuotientGroup.mk' _) ∧ IsSubnormal X ⊤ ∧
          ∀ y : ↥(Subgroup.centralizer {r}),
            (y : G) ∈ ggOTwoPrime (ggG0 p B x L D J ⊓ Subgroup.centralizer {r}) →
              (y : G) ^ p = 1 → QuotientGroup.mk' _ y ∈ X

theorem ggStepThreeChoice_of_rootPlane {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (s2 : GGSixStepTwo p B Bs x L D J)
    {E : Subgroup G} {γ : Fin (ggU t n f).D.rank → ℤ} {u : (ggU t n f).K} {r : G}
    (hEBs : E ≤ Bs) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hγ : GGRootClass (ggU t n f).D t γ)
    (hEX : E ≤ Subgroup.centralizer (ggRootSub (ggU t n f).D ψ γ u : Set G))
    (hrX : r ∈ ggRootSub (ggU t n f).D ψ γ u) (hr : orderOf r = 2)
    (hEf : ∀ e ∈ E, e ≠ 1 → e ∈ D ∨ ∃ L₁ : Subgroup G,
      IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {e}) ∧
        Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2) :
    GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r := by
  obtain ⟨-, ⟨-, -, -, -, -, ⟨hBsN, -⟩, -, -⟩⟩ := hctx
  refine ⟨hEBs, hE, hEcard, ?_, hr, γ, hγ, u, hEX, hrX⟩
  refine ggControlsStrongFusion_of_forall_zpowers (hEBs.trans hBsN) fun e he he1 => ?_
  rcases hEf e he he1 with heD | ⟨L₁, hL₁, hcard⟩
  · exact s1.2.1.of_le (Subgroup.zpowers_le.mpr heD)
  · exact (s2 e (hEBs he) he1 L₁ hL₁ hcard).2

theorem ggSixStepThreeAInput_of_input (h : GGRootPlaneInput) : GGSixStepThreeAInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2
  obtain ⟨E, γ, u, r, hEBs, hE, hEcard, hγ, hEX, hrX, hr, hEf⟩ :=
    h G p B Bs x L D J t n f ψ hctx s1
  exact ⟨E, r, ggStepThreeChoice_of_rootPlane hctx s1 s2 hEBs hE hEcard hγ hEX hrX hr hEf⟩

theorem ggSixRootCentralizer_core {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    {E : Subgroup G} {r : G}
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r) :
    pCoreOf 2 (Subgroup.centralizer {r}) ≤ ggM p B x L D J ∧
      pCoreOf 2 (Subgroup.centralizer {r}) ≤
        pCoreOf 2 (Subgroup.centralizer {r} ⊓ ggM p B x L D J) ∧
      pCoreOf 2 (Subgroup.centralizer {r} ⊓ ggM p B x L D J) ⊓
          Subgroup.centralizer
            (pCoreOf 2 (Subgroup.centralizer {r} ⊓ ggM p B x L D J) : Set G) ≤
        pCoreOf 2 (Subgroup.centralizer {r}) := by
  obtain ⟨⟨-, -, -, hchar, -, hp, -, -⟩, -⟩ := hctx
  have hEr := hch.le_centralizer
  obtain ⟨-, hE, hEcard, hfus, hr, -⟩ := hch
  have hPM := ggPCoreOf_centralizer_le hp.1 hp.2.1 hE hEcard hfus hEr
  have hPQ := ggPCoreOf_le_pCoreOf_inf hPM
  exact ⟨hPM, hPQ, ggInf_centralizer_le_pCoreOf hchar hr
    ((Subgroup.map_subtype_le _).trans inf_le_left) hPQ⟩

theorem exists_mem_oTwoPrime_of_cyclicInput (hcyc : GGRootCentralizerCyclicInput)
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) {E : Subgroup G} {r : G}
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r) :
    ∃ e ∈ E, e ≠ 1 ∧ e ∈ ggOTwoPrime (ggG0 p B x L D J ⊓ Subgroup.centralizer {r}) := by
  have hEr := hch.le_centralizer
  have hroot := hch.rootInvolution
  obtain ⟨⟨-, -, -, -, -, hp, -, -⟩,
    ⟨-, -, ⟨hadm, hrank⟩, ⟨hrange, hker⟩, -, ⟨hBsN, hinn⟩, -, -⟩⟩ := hctx
  obtain ⟨hEBs, hE, hEcard, -⟩ := hch
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hEN : E ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) := hEBs.trans hBsN
  obtain ⟨y₀, hy₀, hEle⟩ := hcyc G t n f ψ hadm hrank hker hC r hroot E
    (le_inf (by rw [hrange]; exact hEN) hEr) fun e he => hinn e (hEBs he)
  rw [hrange] at hEle
  exact ggExists_mem_inf_of_le_sup_zpowers hp.1 hE hEcard
    (ggMem_normalizer_oTwoPrime_inf_centralizer (hEN hy₀) (hEr hy₀)) hEle

theorem centralizer_le_ggM_of_inputs (hcyc : GGRootCentralizerCyclicInput)
    (hsub : GGSixRootCentralizerSubnormalInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (s2 : GGSixStepTwo p B Bs x L D J)
    {E : Subgroup G} {r : G}
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r) :
    Subgroup.centralizer {r} ≤ ggM p B x L D J := by
  obtain ⟨X, hXM, hXN, hX⟩ := hsub G p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  obtain ⟨e, heE, he1, heLQ⟩ := exists_mem_oTwoPrime_of_cyclicInput hcyc hctx s1 hch
  obtain ⟨-, hE, -, hfus, -⟩ := hch
  exact hfus.le_of_isSubnormal heE he1 (hX e heLQ (hE.2 e heE)) hXM hXN

theorem ggSixRootCentralizer_quotientFusion {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    {E : Subgroup G} {r : G}
    (hch : GGStepThreeChoice p Bs (ggM p B x L D J) (ggU t n f).D t ψ E r) :
    GGControlsStrongFusion
      (((ggM p B x L D J).subgroupOf (Subgroup.centralizer {r})).map
        (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r}))))
      ((E.subgroupOf (Subgroup.centralizer {r})).map
        (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥(Subgroup.centralizer {r})))) := by
  have hPM := (ggSixRootCentralizer_core hctx hch).1
  exact ggControlsStrongFusion_quotient hch.2.2.2.1 _
    fun k hk => Subgroup.mem_subgroupOf.mpr (hPM ⟨k, hk, rfl⟩)

theorem ggSixRootCentralizerSubnormalInput_of_quotient (h : GGSixRootCentralizerQuotientInput) :
    GGSixRootCentralizerSubnormalInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  obtain ⟨X, hXM, hXsub, hX⟩ := h G p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  obtain ⟨hle, hsn⟩ :=
    ggExists_subnormal_of_quotient (ggSixRootCentralizer_core hctx hch).1 X hXM hXsub
  refine ⟨_, hle, hsn, fun y hy hyp => ?_⟩
  have hyN : y ∈ Subgroup.centralizer {r} := (ggOTwoPrime_le _ hy).2
  exact ⟨⟨y, hyN⟩, hX ⟨y, hyN⟩ hy hyp, rfl⟩

theorem ggSixStepThreeBInput_of_inputs (hcyc : GGRootCentralizerCyclicInput)
    (hsub : GGSixRootCentralizerSubnormalInput) : GGSixStepThreeBInput :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hctx s1 s2 _ _ hch =>
    centralizer_le_ggM_of_inputs hcyc hsub hctx s1 s2 hch

theorem ggSecSixV2Input_of_rootCentralizer (h1 : GGSixStepOneV2Input)
    (h2 : GGSixStepTwoV2Input) (h3a : GGRootPlaneInput) (hcyc : GGRootCentralizerCyclicInput)
    (hsub : GGSixRootCentralizerSubnormalInput) (h3c : GGSixStepThreeCInput)
    (h3d : GGSixStepThreeDInput) (hKG : GGRootInvolutionCentralInput) : GGSecSixV2Input :=
  ggSecSixV2Input_of_inputs h1 h2 (ggSixStepThreeAInput_of_input h3a)
    (ggSixStepThreeBInput_of_inputs hcyc hsub) h3c h3d hKG

theorem ggSixRootCentralizerQuotientInput_of_subnormal (h : GGSixRootCentralizerSubnormalInput) :
    GGSixRootCentralizerQuotientInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  obtain ⟨X, hXM, hXN, hX⟩ := h G p B Bs x L D J t n f ψ hctx s1 s2 E r hch
  set N := Subgroup.centralizer ({r} : Set G)
  have hsub : IsSubnormal (X.subgroupOf N) ⊤ := by
    have : IsSubnormal (X.subgroupOf N) (N.subgroupOf N) := ggIsSubnormal_comap N.subtype hXN
    rwa [Subgroup.subgroupOf_self] at this
  have hmap := ggIsSubnormal_map (QuotientGroup.mk' (CFSG.Assembly.pCore 2 ↥N)) hsub
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hmap
  refine ⟨_, Subgroup.map_mono fun y hy => Subgroup.mem_subgroupOf.mpr
    (hXM (Subgroup.mem_subgroupOf.mp hy)), hmap, fun y hy hyp =>
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hX y hy hyp))⟩

theorem ggSixStepThreeBInput_of_quotient (hcyc : GGRootCentralizerCyclicInput)
    (hq : GGSixRootCentralizerQuotientInput) : GGSixStepThreeBInput :=
  ggSixStepThreeBInput_of_inputs hcyc (ggSixRootCentralizerSubnormalInput_of_quotient hq)

end Inputs

end CFSG.StandardType

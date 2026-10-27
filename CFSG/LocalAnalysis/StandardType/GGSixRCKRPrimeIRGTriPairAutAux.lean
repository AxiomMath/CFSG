module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4BridgeIso
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainX
public import CFSG.LieType.AschbacherSeitz.RootGroupTransport
public import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.AschbacherSeitz CFSG.StandardType.AutSt
open CFSG.StandardType.LieKnownR2.TriD4.Bridge

noncomputable abbrev irgTA_sigmaEquiv {K : Type} [Field K] [Finite K] (σ : K →+* K) :
    K ≃+* K :=
  RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩

theorem irgTA_sigmaEquiv_apply {K : Type} [Field K] [Finite K] (σ : K →+* K) (c : K) :
    irgTA_sigmaEquiv σ c = σ c := rfl

theorem irgTA_comm_of_finite {K : Type} [Field K] [Finite K]
    (σ : K →+* K) (δ : K ≃+* K) (c : K) : δ (σ c) = σ (δ c) := by
  have h := ringEquiv_comm_of_finite (irgTA_sigmaEquiv σ) δ c
  rwa [irgTA_sigmaEquiv_apply] at h

theorem irgTA_twistC_entrywise_comm
    {K : Type} [Field K] (σ : K →+* K) (δ : K ≃+* K)
    (hδ : ∀ c, δ (σ c) = σ (δ c)) (x : adjointGroup TwistTag.D4.tag K) :
    twistC TwistTag.D4 K σ (entrywiseAdjointAut TwistTag.D4.tag δ x) =
      entrywiseAdjointAut TwistTag.D4.tag δ (twistC TwistTag.D4 K σ x) := by
  apply Subtype.ext
  show twistHom TwistTag.D4 K σ
      ((entrywiseAdjointAut TwistTag.D4.tag δ x : adjointGroup TwistTag.D4.tag K) :
        ModGL TwistTag.D4.tag K) =
    ((entrywiseAdjointAut TwistTag.D4.tag δ (twistC TwistTag.D4 K σ x) :
        adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K)
  rw [coe_entrywiseAdjointAut, coe_entrywiseAdjointAut,
    coe_twistC]
  exact twistHom_units_map_entrywiseHom hδ (x : ModGL TwistTag.D4.tag K)

theorem irgTA_map_twistedRootSubgroupD4_entrywise
    {K : Type} [Field K] [Finite K] (σ : K →+* K) (δ : K ≃+* K)
    (β : Fin (Tag.rank .G2) → ℤ) :
    Subgroup.map (entrywiseAdjointAut TwistTag.D4.tag δ).toMonoidHom
        (twistedRootSubgroupD4 σ β) = twistedRootSubgroupD4 σ β := by
  have hδ : ∀ c, δ (σ c) = σ (δ c) := irgTA_comm_of_finite σ δ
  have hf : Function.Injective (entrywiseAdjointAut TwistTag.D4.tag δ).toMonoidHom :=
    (entrywiseAdjointAut TwistTag.D4.tag δ).injective
  rw [twistedRootSubgroupD4, twistedRootSubgroup,
    Subgroup.map_inf_eq _ _ _ hf]
  congr 1
  · rw [Subgroup.map_iSup]
    apply iSup_congr
    intro α
    rw [Subgroup.map_iSup]
    apply iSup_congr
    intro hα
    rw [Subgroup.map_iSup]
    apply iSup_congr
    intro _
    exact CFSG.LieType.AschbacherSeitz.entrywise_rootGroup_map_eq
        (F := rootOperatorFamily TwistTag.D4.tag) δ hα
  · apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hx' : twistC TwistTag.D4 K σ x = x := hx
      show twistC TwistTag.D4 K σ (entrywiseAdjointAut TwistTag.D4.tag δ x) =
        entrywiseAdjointAut TwistTag.D4.tag δ x
      rw [irgTA_twistC_entrywise_comm σ δ hδ x, hx']
    · intro y hy
      refine Subgroup.mem_map.2 ⟨entrywiseAdjointAut TwistTag.D4.tag δ.symm y, ?_, ?_⟩
      · show twistC TwistTag.D4 K σ (entrywiseAdjointAut TwistTag.D4.tag δ.symm y) =
          entrywiseAdjointAut TwistTag.D4.tag δ.symm y
        have hy' : twistC TwistTag.D4 K σ y = y := hy
        rw [irgTA_twistC_entrywise_comm σ δ.symm (irgTA_comm_of_finite σ δ.symm) y, hy']
      · have hmul : entrywiseAdjointAut TwistTag.D4.tag δ *
            entrywiseAdjointAut TwistTag.D4.tag δ.symm = 1 := by
          rw [← entrywiseAdjointAut_mul]
          have h1 : δ * δ.symm = 1 := by
            ext c
            simp
          rw [h1, entrywiseAdjointAut_one]
        have h2 := congrArg
          (fun e : MulAut (adjointGroup TwistTag.D4.tag K) => e y) hmul
        change (entrywiseAdjointAut TwistTag.D4.tag δ)
          ((entrywiseAdjointAut TwistTag.D4.tag δ.symm) y) = y
        simpa only [MulAut.mul_apply, MulAut.one_apply] using h2


noncomputable abbrev irgTA_bridge
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g) :
    twistedGroup σ ≃* graphFixedRootGroup TwistTag.D4 F (irgTA_sigmaEquiv σ).toRingHom :=
  (triD4BridgeEquiv σ hT.1 hT.2.1 hT.2.2).trans
    (MulEquiv.subgroupCongr (by rfl))

theorem irgTA_bridge_coe
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g)
    (x : twistedGroup σ) :
    (((irgTA_bridge hT) x :
        graphFixedRootGroup TwistTag.D4 F (irgTA_sigmaEquiv σ).toRingHom) :
        ModGL TwistTag.D4.tag F) =
      ((x : adjointGroup TwistTag.D4.tag F) : ModGL TwistTag.D4.tag F) :=
  triD4BridgeEquiv_coe σ hT.1 hT.2.1 hT.2.2 x

theorem irgTA_bridge_symm_coe
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g)
    (y : graphFixedRootGroup TwistTag.D4 F (irgTA_sigmaEquiv σ).toRingHom) :
    ((((irgTA_bridge hT).symm y : twistedGroup σ) : adjointGroup TwistTag.D4.tag F) :
        ModGL TwistTag.D4.tag F) = (y : ModGL TwistTag.D4.tag F) :=
  congrArg (fun z : graphFixedRootGroup TwistTag.D4 F (irgTA_sigmaEquiv σ).toRingHom =>
      (z : ModGL TwistTag.D4.tag F)) (MulEquiv.apply_symm_apply (irgTA_bridge hT) y)

noncomputable abbrev irgTA_fieldPart
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g)
    (δ : F ≃+* F) : MulAut (twistedGroup σ) :=
  (irgTA_bridge hT).trans
    (((fieldActor (irgTA_sigmaEquiv σ) δ).trans (irgTA_bridge hT).symm))

noncomputable abbrev irgTA_alphaZero
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g)
    (α : MulAut (twistedGroup σ)) :
    MulAut (graphFixedRootGroup TwistTag.D4 F (irgTA_sigmaEquiv σ).toRingHom) :=
  (irgTA_bridge hT).symm.trans (α.trans (irgTA_bridge hT))

theorem irgTA_fieldPart_coe
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g)
    (δ : F ≃+* F) (x : twistedGroup σ) :
    ((irgTA_fieldPart hT δ x : twistedGroup σ) : adjointGroup TwistTag.D4.tag F) =
      entrywiseAdjointAut TwistTag.D4.tag δ (x : adjointGroup TwistTag.D4.tag F) := by
  apply Subtype.ext
  dsimp only [irgTA_fieldPart]
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply,
    irgTA_bridge_symm_coe hT, coe_fieldActor, irgTA_bridge_coe,
    coe_entrywiseAdjointAut]

theorem irgTA_fieldPart_map
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g)
    (δ : F ≃+* F) {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β) :
    Subgroup.map (irgTA_fieldPart hT δ).toMonoidHom (twistedRootGroup σ β) =
      twistedRootGroup σ β := by
  have hX := irgTA_map_twistedRootSubgroupD4_entrywise σ δ β
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    change (irgTA_fieldPart hT δ x : adjointGroup TwistTag.D4.tag F) ∈
      twistedRootSubgroupD4 σ β
    rw [irgTA_fieldPart_coe hT δ x]
    have hx' : (x : adjointGroup TwistTag.D4.tag F) ∈ twistedRootSubgroupD4 σ β := hx
    have hmem : entrywiseAdjointAut TwistTag.D4.tag δ
          (x : adjointGroup TwistTag.D4.tag F) ∈
        Subgroup.map (entrywiseAdjointAut TwistTag.D4.tag δ).toMonoidHom
          (twistedRootSubgroupD4 σ β) := Subgroup.mem_map_of_mem _ hx'
    rwa [hX] at hmem
  · intro y hy
    change (y : adjointGroup TwistTag.D4.tag F) ∈ twistedRootSubgroupD4 σ β at hy
    rw [← hX] at hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
    let x : twistedGroup σ := ⟨z, twistedRootSubgroupD4_le_twistedGroup σ hβ hz⟩
    refine ⟨x, ?_, ?_⟩
    · change (x : adjointGroup TwistTag.D4.tag F) ∈ twistedRootSubgroupD4 σ β
      exact hz
    · apply Subtype.ext
      change ((irgTA_fieldPart hT δ x : twistedGroup σ) :
        adjointGroup TwistTag.D4.tag F) = (y : adjointGroup TwistTag.D4.tag F)
      rw [irgTA_fieldPart_coe hT δ x]
      exact hzy

theorem irgTA_exists_normalForm
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g)
    (α : MulAut (twistedGroup σ)) :
    ∃ (g₀ : graphFixedRootGroup TwistTag.D4 F (irgTA_sigmaEquiv σ).toRingHom) (δ : F ≃+* F),
      α = MulAut.conj ((irgTA_bridge hT).symm g₀) * irgTA_fieldPart hT δ ∧
      ∀ x : twistedGroup σ,
        α x = (irgTA_bridge hT).symm g₀ * irgTA_fieldPart hT δ x *
          ((irgTA_bridge hT).symm g₀)⁻¹ := by
  let α₀ := irgTA_alphaZero hT α
  obtain ⟨⟨g₀, δ⟩, hg₀, -⟩ :=
    (even_triality_exact_automorphism_normal_form (f := g) hT.1 F hT.2.1
      (irgTA_sigmaEquiv σ) hT.2.2).2.1 α₀
  have hfield : ∀ x : twistedGroup σ,
      fieldActor (irgTA_sigmaEquiv σ) δ ((irgTA_bridge hT) x) =
        (irgTA_bridge hT) (irgTA_fieldPart hT δ x) := by
    intro x
    apply Subtype.ext
    rw [coe_fieldActor, irgTA_bridge_coe, irgTA_bridge_coe, irgTA_fieldPart_coe,
      coe_entrywiseAdjointAut]
  have hαx : ∀ x : twistedGroup σ,
      α x = (irgTA_bridge hT).symm g₀ * irgTA_fieldPart hT δ x *
        ((irgTA_bridge hT).symm g₀)⁻¹ := by
    intro x
    have h1 : α₀ ((irgTA_bridge hT) x) = (irgTA_bridge hT) (α x) := by
      dsimp only [α₀, irgTA_alphaZero]
      rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply]
    rw [← (irgTA_bridge hT).symm_apply_apply (α x), ← h1, hg₀]
    rw [MulAut.mul_apply, MulAut.conj_apply]
    rw [hfield x]
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  refine ⟨g₀, δ, ?_, hαx⟩
  apply MulEquiv.ext
  intro x
  simpa only [MulAut.mul_apply, MulAut.conj_apply] using hαx x

theorem irgTA_exists_conj_map_twistedRootGroup
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g)
    (α : MulAut (twistedGroup σ)) :
    ∃ t : twistedGroup σ, ∀ (β : Fin (Tag.rank .G2) → ℤ), IsRoot .G2 β →
      Subgroup.map α.toMonoidHom (twistedRootGroup σ β) =
        Subgroup.map (MulAut.conj t).toMonoidHom (twistedRootGroup σ β) := by
  obtain ⟨g₀, δ, -, hαx⟩ := irgTA_exists_normalForm hT α
  refine ⟨(irgTA_bridge hT).symm g₀, fun β hβ => ?_⟩
  have hφ : Subgroup.map (irgTA_fieldPart hT δ).toMonoidHom (twistedRootGroup σ β) =
      twistedRootGroup σ β := irgTA_fieldPart_map hT δ hβ
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine Subgroup.mem_map.2 ⟨irgTA_fieldPart hT δ x, ?_, ?_⟩
    · rw [← hφ]
      exact Subgroup.mem_map_of_mem (irgTA_fieldPart hT δ).toMonoidHom hx
    · change MulAut.conj ((irgTA_bridge hT).symm g₀) (irgTA_fieldPart hT δ x) = α x
      simpa only [MulAut.conj_apply] using (hαx x).symm
  · rintro y ⟨x, hx, rfl⟩
    rw [← hφ] at hx
    obtain ⟨x', hx', hφx'⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨x', hx', ?_⟩
    change α x' = MulAut.conj ((irgTA_bridge hT).symm g₀) x
    have hφx'' : irgTA_fieldPart hT δ x' = x := hφx'
    rw [hαx x', hφx'']
    rfl

end CFSG.StandardType.RCKRP

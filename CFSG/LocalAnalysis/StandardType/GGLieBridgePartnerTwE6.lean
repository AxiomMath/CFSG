module

public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHom
public import CFSG.LocalAnalysis.StandardType.GGLieCoreBridge
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGFinModelTw
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Lang
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcTwE6Cyc

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

private theorem l10b6_partner_of_induces {L C G Y : Type} [Group L] [Group C] [Group G] [Group Y]
    {ψ : L →* G} {G₀ : Subgroup G} (hrange : ψ.range = G₀) (π : L →* C) (ρ : C →* Y)
    {θ : ↥G₀ →* Y} (hθ : ∀ (k : L) (h : ψ k ∈ G₀), θ ⟨ψ k, h⟩ = ρ (π k)) {d : G}
    {α : MulAut C} (hα : LayerSixE.GGInduces π ψ d α) {a : Y}
    (ha : ∀ c : C, ρ (α c) = a * ρ c * a⁻¹) : GGLiePartner G₀ θ d a := by
  intro x h
  obtain ⟨k, hk⟩ : ∃ k, ψ k = (x : G) := by
    have hx : (x : G) ∈ ψ.range := by rw [hrange]; exact x.2
    exact MonoidHom.mem_range.mp hx
  obtain ⟨k', hk'⟩ : ∃ k', ψ k' = d * ψ k * d⁻¹ := by
    have hmem : d * ψ k * d⁻¹ ∈ ψ.range := by
      rw [hrange, hk]
      exact h
    exact MonoidHom.mem_range.mp hmem
  have hπ : π k' = α (π k) := hα k k' hk'
  have hxsub : (⟨ψ k, by rw [hk]; exact x.2⟩ : ↥G₀) = x := Subtype.ext hk
  have hxθ : θ x = ρ (π k) := by
    rw [← hxsub]
    exact hθ k (by rw [hk]; exact x.2)
  have hdθ : θ ⟨d * (x : G) * d⁻¹, h⟩ = ρ (π k') := by
    have h' : ψ k' ∈ G₀ := by rw [← hrange]; exact ⟨k', rfl⟩
    have hsub : (⟨ψ k', h'⟩ : ↥G₀) = ⟨d * (x : G) * d⁻¹, h⟩ := by
      apply Subtype.ext
      simp only [Subtype.coe_mk]
      rw [hk', hk]
    rw [← hsub]
    exact hθ k' h'
  rw [hdθ, hπ, ha, hxθ]

private theorem l10b6_induces
    {n f : ℕ} (hf : 1 ≤ f) {G : Type} [Group G] {ψ : (ggU .twistedE6 n f).K →* G}
    {G₀ : Subgroup G} (hpres : GGPresentsG0 G₀ (ggU .twistedE6 n f).D .twistedE6 n f ψ) {d : G}
    (hd : d ∈ Subgroup.normalizer (G₀ : Set G))
    (hψ : GGPsiInnerDiag (ggU .twistedE6 n f).D ψ d) :
    ∃ π : twistedE6Group 2 f →*
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      (∀ z, ((π z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) ∧
      ∃ α ∈ LayerSixE.twInndiagAut f, LayerSixE.GGInduces π ψ d α := by
  obtain ⟨π, -, hπker, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f) := hpres.2.1.2
  have hkπ : ψ.ker ≤ π.ker := hker.trans hπker.ge
  have hcN : d ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hpres.2.1.1]
    exact hd
  exact ⟨π, hπval, LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ hcN hψ⟩

private theorem l10b6_alpha_form
    {f : ℕ} {α : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hα : α ∈ LayerSixE.twInndiagAut f) :
    ∃ (g : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (b : ↥(TableB.TwE6.compat (frobQ 2 f))),
      α = MulAut.conj g * RootCentExc.compatParamAut (frobQ 2 f) b := by
  haveI : (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range.Normal :=
    RootCentExc.normal_range_mulAutConj
  unfold LayerSixE.twInndiagAut at hα
  rw [Subgroup.mem_sup_of_normal_left] at hα
  obtain ⟨g, hg, z, hz, rfl⟩ := hα
  obtain ⟨g', rfl⟩ := hg
  obtain ⟨b, rfl⟩ := hz
  exact ⟨g', b, rfl⟩

private theorem l10b6_mem_fix
    {f : ℕ} (hf : 1 ≤ f)
    (g : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (b : ↥(TableB.TwE6.compat (frobQ 2 f))) :
    baseChangeGL (ggRatEmb (2 * f))
        ((g : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
          rootDiagUnit TwistTag.E6.tag (b : Fin 6 → (GaloisField 2 (2 * f))ˣ)) ∈
      ggFixGp .twistedE6 f := by
  classical
  let F := GaloisField 2 (2 * f)
  let σ : F →+* F := frobQ 2 f
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra F GGL := (ggRatEmb (2 * f)).toAlgebra
  haveI : IsScalarTower (ZMod 2) F GGL := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.IsAlgebraic F GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := F) (A := GGL)
  haveI : IsAlgClosure F GGL := ⟨IsAlgClosure.isAlgClosed (ZMod 2), inferInstance⟩
  have hσsurj : Function.Surjective σ :=
    Finite.surjective_of_injective σ.injective
  let σE : F ≃+* F := RingEquiv.ofBijective σ ⟨σ.injective, hσsurj⟩
  have hσE : ∀ c, σE c = c ^ (2 ^ f) := fun c => by
    change frobQ 2 f c = c ^ (2 ^ f)
    exact frobQ_apply 2 f c
  have hb : RecipeExcLang.IsCompatE6 σE.toRingHom (b : Fin 6 → Fˣ) := fun i => b.2 i
  have hw : (g : ModGL TwistTag.E6.tag F) *
      rootDiagUnit TwistTag.E6.tag (b : Fin 6 → Fˣ) ∈
        RecipeExcLang.twInndiagGroup F σE :=
    mul_mem (RecipeExcLang.graphFixedRootGroup_le_twInndiag σE g.2)
      (RecipeExcLang.rootDiagUnit_mem_twInndiag hb)
  change baseChangeGL (algebraMap F GGL)
      ((g : ModGL TwistTag.E6.tag F) *
        rootDiagUnit TwistTag.E6.tag (b : Fin 6 → Fˣ)) ∈
      twistedFixedGroup TwistTag.E6 GGL (ggFrobT f)
  exact RecipeExcLang.baseChangeGL_mem_twistedFixed_of_mem_twInndiag (K := F) (L := GGL)
    (n := f) hf (card_galoisField_two_mul 2 f hf) hσE (ggFrobT_apply f) hw

private theorem l10b6_act
    {f : ℕ} (g : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
    (b : ↥(TableB.TwE6.compat (frobQ 2 f)))
    (u : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
    baseChangeGL (ggRatEmb (2 * f))
        (((MulAut.conj g * RootCentExc.compatParamAut (frobQ 2 f) b) u :
          ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      baseChangeGL (ggRatEmb (2 * f))
          ((g : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
            rootDiagUnit TwistTag.E6.tag (b : Fin 6 → (GaloisField 2 (2 * f))ˣ)) *
        baseChangeGL (ggRatEmb (2 * f)) (u : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        (baseChangeGL (ggRatEmb (2 * f))
          ((g : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
            rootDiagUnit TwistTag.E6.tag (b : Fin 6 → (GaloisField 2 (2 * f))ˣ)))⁻¹ := by
  have hcoe : (((MulAut.conj g * RootCentExc.compatParamAut (frobQ 2 f) b) u :
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      (g : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
        (rootDiagUnit TwistTag.E6.tag (b : Fin 6 → (GaloisField 2 (2 * f))ˣ) *
          (u : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) *
          (rootDiagUnit TwistTag.E6.tag (b : Fin 6 → (GaloisField 2 (2 * f))ˣ))⁻¹) *
        (g : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))⁻¹ := by
    rw [MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, RootCentExc.coe_compatParamAut_apply]
  rw [hcoe]
  simp only [map_mul, map_inv, mul_inv_rev, mul_assoc]

private theorem l10b6_iotaK_eq
    {n f : ℕ} (hf : 1 ≤ f)
    {π : twistedE6Group 2 f →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hπ : ∀ z, ((π z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        ((e6IsogenyT (GaloisField 2 (2 * f)) (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
    (k : (ggU .twistedE6 n f).K) :
    ggIotaK .twistedE6 n f hf k =
      baseChangeGL (ggRatEmb (2 * f))
        ((π k : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) := by
  show ggIota .twistedE6 n f hf (QuotientGroup.mk k) =
    baseChangeGL (ggRatEmb (2 * f))
      ((π k : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))
  rw [ggIota_twistedE6_mk]
  exact congrArg (baseChangeGL (ggRatEmb (2 * f))) (hπ k).symm

theorem ggLiePartner_twistedE6
    {t : StatedLieTag} {n f : ℕ} (ht : t = .twistedE6)
    (hf : 1 ≤ f) {G : Type} [Group G] {ψ : (ggU t n f).K →* G} {G₀ : Subgroup G}
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ) {θ : ↥G₀ →* ModGL (langTag t) GGL}
    (hθ : ∀ (k : (ggU t n f).K) (h : ψ k ∈ G₀), θ ⟨ψ k, h⟩ = ggIotaK t n f hf k)
    {d : G} (hd : d ∈ Subgroup.normalizer (G₀ : Set G))
    (hψ : GGPsiInnerDiag (ggU t n f).D ψ d) :
    ∃ a ∈ ggFixGp t f, GGLiePartner G₀ θ d a := by
  subst ht
  obtain ⟨π, hπ, α, hα, hαind⟩ := l10b6_induces hf hpres hd hψ
  obtain ⟨g, b, rfl⟩ := l10b6_alpha_form hα
  refine ⟨_, l10b6_mem_fix hf g b, l10b6_partner_of_induces hpres.2.1.1
    π ((baseChangeGL (ggRatEmb (2 * f))).comp
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype)
    (fun k h => (hθ k h).trans (l10b6_iotaK_eq hf hπ k)) hαind (fun u => l10b6_act g b u)⟩

end CFSG.StandardType.LieCore

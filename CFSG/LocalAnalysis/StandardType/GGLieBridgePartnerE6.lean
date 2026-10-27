module

public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHom
public import CFSG.LocalAnalysis.StandardType.GGLieCoreBridge
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEMain
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructE6Diag
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangCore

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

private theorem l10b5_partner_of_induces {L C G Y : Type} [Group L] [Group C] [Group G] [Group Y]
    {ψ : L →* G} {G₀ : Subgroup G} (hrange : ψ.range = G₀) (π : L →* C) (ρ : C →* Y)
    {θ : ↥G₀ →* Y} (hθ : ∀ (k : L) (h : ψ k ∈ G₀), θ ⟨ψ k, h⟩ = ρ (π k)) {d : G}
    {α : MulAut C} (hα : LayerSixE.GGInduces π ψ d α) {a : Y}
    (ha : ∀ c : C, ρ (α c) = a * ρ c * a⁻¹) : GGLiePartner G₀ θ d a := by
  intro x h
  have hx : (x : G) ∈ ψ.range := hrange.symm ▸ x.2
  obtain ⟨k, hk⟩ := hx
  have hmem : d * ψ k * d⁻¹ ∈ ψ.range := by
    rw [hrange, hk]
    exact h
  have hmemG : d * ψ k * d⁻¹ ∈ G₀ := hrange ▸ hmem
  obtain ⟨k', hk'⟩ := hmem
  have hd : d * (x : G) * d⁻¹ = ψ k' := by rw [← hk, ← hk']
  have hm' : ψ k' ∈ G₀ := hk' ▸ hmemG
  calc
    θ ⟨d * (x : G) * d⁻¹, h⟩ = θ ⟨ψ k', hm'⟩ := congrArg θ (Subtype.ext hd)
    _ = ρ (π k') := hθ k' hm'
    _ = ρ (α (π k)) := by rw [hα k k' hk']
    _ = a * ρ (π k) * a⁻¹ := ha (π k)
    _ = a * θ x * a⁻¹ := by
      have hx' : x = ⟨ψ k, hk ▸ x.2⟩ := Subtype.ext hk.symm
      rw [hx', hθ k (hk ▸ x.2)]

private theorem l10b5_induces
    {n f : ℕ} {G : Type} [Group G] {ψ : (ggU .E6 n f).K →* G}
    {G₀ : Subgroup G} (hpres : GGPresentsG0 G₀ (ggU .E6 n f).D .E6 n f ψ) {d : G}
    (hd : d ∈ Subgroup.normalizer (G₀ : Set G))
    (hψ : GGPsiInnerDiag (ggU .E6 n f).D ψ d) :
    ∃ α ∈ LayerSixE.inndiagAut .E6 (GaloisField 2 f),
      LayerSixE.GGInduces (e6Isogeny (GaloisField 2 f)) ψ d α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd' : d ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hpres.2.1.1]; exact hd
  exact LayerSixE.exists_induces_E6 ψ hpres.2.1.2 hd' hψ

private theorem l10b5_alpha_form
    {f : ℕ} {α : MulAut ↥(adjointGroup Tag.E6 (GaloisField 2 f))}
    (hα : α ∈ LayerSixE.inndiagAut .E6 (GaloisField 2 f)) :
    ∃ (g : ↥(adjointGroup Tag.E6 (GaloisField 2 f))) (a : Fin Tag.E6.rank → (GaloisField 2 f)ˣ),
      α = MulAut.conj g * rootDiagAutHom .E6 (GaloisField 2 f) a := by
  exact KGE6.mem_innDiag_iff.1 hα

private theorem l10b5_mem_fix
    {f : ℕ} (hf : 1 ≤ f) (g : ↥(adjointGroup Tag.E6 (GaloisField 2 f)))
    (a : Fin Tag.E6.rank → (GaloisField 2 f)ˣ) :
    baseChangeGL (ggRatEmb f)
        ((g : ModGL Tag.E6 (GaloisField 2 f)) * rootDiagUnit Tag.E6 a) ∈ ggFixGp .E6 f := by
  let k := GaloisField 2 f
  let w : ModGL Tag.E6 k := (g : ModGL Tag.E6 k) * rootDiagUnit Tag.E6 a
  have hw : w ∈ RecipeExcLang.inndiagGroup Tag.E6 k :=
    mul_mem (RecipeExcLang.adjointGroup_le_inndiagGroup g.2)
      (RecipeExcLang.rootDiagUnit_mem_inndiagGroup a)
  have hcard : Nat.card k = 2 ^ f := GaloisField.card 2 f (by omega)
  have hFr : ∀ c : GGL, ggFrobT f c = c ^ Nat.card k := by
    intro c
    rw [ggFrobT_apply, hcard]
  letI : Algebra k GGL := (ggRatEmb f).toAlgebra
  have hfix : Units.map (entrywiseHom (ggFrobT f)) (baseChangeGL (ggRatEmb f) w) =
      baseChangeGL (ggRatEmb f) w := by
    simpa only [RingHom.algebraMap_toAlgebra] using
      (units_map_entrywiseHom_baseChangeGL_algebraMap (k := k) (L := GGL)
        (ggFrobT f) hFr w)
  rw [ggFixGp]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · show baseChangeGL (ggRatEmb f) w ∈ adjointGroup Tag.E6 GGL
    exact RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag (ggRatEmb f) hw
  · change Units.map (entrywiseHom (ggFrobT f)) (baseChangeGL (ggRatEmb f) w) =
      MonoidHom.id _ (baseChangeGL (ggRatEmb f) w)
    simpa only [MonoidHom.id_apply] using hfix

private theorem l10b5_act
    {f : ℕ} (g : ↥(adjointGroup Tag.E6 (GaloisField 2 f)))
    (a : Fin Tag.E6.rank → (GaloisField 2 f)ˣ) (u : ↥(adjointGroup Tag.E6 (GaloisField 2 f))) :
    baseChangeGL (ggRatEmb f)
        (((MulAut.conj g * rootDiagAutHom .E6 (GaloisField 2 f) a) u :
          ↥(adjointGroup Tag.E6 (GaloisField 2 f))) : ModGL Tag.E6 (GaloisField 2 f)) =
      baseChangeGL (ggRatEmb f)
          ((g : ModGL Tag.E6 (GaloisField 2 f)) * rootDiagUnit Tag.E6 a) *
        baseChangeGL (ggRatEmb f) (u : ModGL Tag.E6 (GaloisField 2 f)) *
        (baseChangeGL (ggRatEmb f)
          ((g : ModGL Tag.E6 (GaloisField 2 f)) * rootDiagUnit Tag.E6 a))⁻¹ := by
  have hinner : (((MulAut.conj g * rootDiagAutHom .E6 (GaloisField 2 f) a) u :
      ↥(adjointGroup Tag.E6 (GaloisField 2 f))) : ModGL Tag.E6 (GaloisField 2 f)) =
      (g : ModGL Tag.E6 (GaloisField 2 f)) * rootDiagUnit Tag.E6 a *
        (u : ModGL Tag.E6 (GaloisField 2 f)) *
        ((g : ModGL Tag.E6 (GaloisField 2 f)) * rootDiagUnit Tag.E6 a)⁻¹ := by
    change (((MulAut.conj g * rootDiagAut .E6 (GaloisField 2 f) a) u :
      ↥(adjointGroup Tag.E6 (GaloisField 2 f))) : ModGL Tag.E6 (GaloisField 2 f)) =
      (g : ModGL Tag.E6 (GaloisField 2 f)) * rootDiagUnit Tag.E6 a *
        (u : ModGL Tag.E6 (GaloisField 2 f)) *
        ((g : ModGL Tag.E6 (GaloisField 2 f)) * rootDiagUnit Tag.E6 a)⁻¹
    simp only [MulAut.mul_apply, MulAut.conj_apply, coe_rootDiagAut, Subgroup.coe_mul,
      Subgroup.coe_inv]
    group
  rw [hinner, map_mul, map_mul, map_inv]

private theorem l10b5_iotaK_eq
    {n f : ℕ} (hf : 1 ≤ f) (k : (ggU .E6 n f).K) :
    ggIotaK .E6 n f hf k =
      baseChangeGL (ggRatEmb f)
        ((e6Isogeny (GaloisField 2 f) k : ↥(adjointGroup Tag.E6 (GaloisField 2 f))) :
          ModGL Tag.E6 (GaloisField 2 f)) := by
  exact ggIota_E6_mk n f hf k

theorem ggLiePartner_E6
    {t : StatedLieTag} {n f : ℕ} (ht : t = .E6)
    (hf : 1 ≤ f) {G : Type} [Group G] {ψ : (ggU t n f).K →* G} {G₀ : Subgroup G}
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ) {θ : ↥G₀ →* ModGL (langTag t) GGL}
    (hθ : ∀ (k : (ggU t n f).K) (h : ψ k ∈ G₀), θ ⟨ψ k, h⟩ = ggIotaK t n f hf k)
    {d : G} (hd : d ∈ Subgroup.normalizer (G₀ : Set G))
    (hψ : GGPsiInnerDiag (ggU t n f).D ψ d) :
    ∃ a ∈ ggFixGp t f, GGLiePartner G₀ θ d a := by
  subst ht
  obtain ⟨α, hα, hαind⟩ := l10b5_induces hpres hd hψ
  obtain ⟨g, a, rfl⟩ := l10b5_alpha_form hα
  exact ⟨_, l10b5_mem_fix hf g a, l10b5_partner_of_induces hpres.2.1.1
    (e6Isogeny (GaloisField 2 f))
    ((baseChangeGL (ggRatEmb f)).comp (adjointGroup Tag.E6 (GaloisField 2 f)).subtype)
    (fun k h => (hθ k h).trans (l10b5_iotaK_eq hf k)) hαind (fun u => l10b5_act g a u)⟩

end CFSG.StandardType.LieCore

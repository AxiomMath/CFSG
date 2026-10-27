module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4Inner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4NC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverNC
public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainX
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.RouteD.NonClassicalShape

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.StandardType.S2MathFi1035Pos (TriField triD4Universal)
open scoped commutatorElement

namespace CFSG.StandardType.LieKnownR2.TriD4

private theorem tforms_GGLongRoot_mem_roots {U : Type} [Group U] {Δ : UniversalRootDatum U}
    {γ : Fin Δ.rank → ℤ} (hγ : GGLongRoot Δ γ) : γ ∈ Δ.roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := hγ
  exact CFSG.LieType.RootSystem.weylAction_mem_roots Δ.isFiniteType w hγ₀

private theorem tforms_inner_top {K : Type} [Group K] {R : Subgroup K}
    (h : GGRootNormInner R) : GGRootNormInner (R.subgroupOf ⊤) := by
  have he : R.map (Subgroup.topEquiv.symm : K ≃* ↥(⊤ : Subgroup K)).toMonoidHom =
      R.subgroupOf ⊤ := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
    simp
  rw [← he]
  exact ggRootNormInner_map_mulEquiv _ h

private theorem tforms_ker_eq_bot
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g)
    {X : Type} [Group X] (φ : (triD4Universal F σ).K →* X)
    (hker : φ.ker ≤ Subgroup.center (triD4Universal F σ).K) : φ.ker = ⊥ := by
  rcases hF with ⟨hg, hcard, hσ⟩
  have hcenter : Subgroup.center (triD4Universal F σ).K = ⊥ := by
    change Subgroup.center ↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ) = ⊥
    exact CFSG.ClassicalInvolution.RouteD.center_twistedGroup_eq_bot_of_card (p := 2) (e := g)
      σ Nat.prime_two hg hcard hσ
  exact le_bot_iff.mp (hker.trans (le_of_eq hcenter))

private theorem tforms_inner_range
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g)
    {X : Type} [Group X] (φ : (triD4Universal F σ).K →* X)
    (hker : φ.ker ≤ Subgroup.center (triD4Universal F σ).K)
    {β : Fin (triD4Universal F σ).D.rank → ℤ} (hl : GGLongRoot (triD4Universal F σ).D β)
    (u : (triD4Universal F σ).K) :
    GGRootNormInner ((ggRootSub (triD4Universal F σ).D φ β u).subgroupOf φ.range) := by
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact tforms_ker_eq_bot hF φ hker
  have hcontract : GGRootNormInner
      (((triD4Universal F σ).D.rootGroup β).map (MulAut.conj u).toMonoidHom) :=
    ggRootNormInner_triD4 hF hl u
  have htop : GGRootNormInner
      ((ggRootSub (triD4Universal F σ).D (MonoidHom.id _) β u).subgroupOf ⊤) := by
    have h1 : ggRootSub (triD4Universal F σ).D (MonoidHom.id _) β u =
        (((triD4Universal F σ).D.rootGroup β).map (MulAut.conj u).toMonoidHom) := by
      simp only [ggRootSub, Subgroup.map_id]
    rw [h1]
    exact tforms_inner_top hcontract
  refine ggRootNormInner_of_map_injective φ hφ
    (K' := ⊤) (R' := ggRootSub (triD4Universal F σ).D (MonoidHom.id _) β u)
    (K := φ.range) (R := ggRootSub (triD4Universal F σ).D φ β u) ?_ ?_ htop
  · rw [Subgroup.map_top]
  · simp only [ggRootSub, Subgroup.map_id]

theorem ggRootInnerAt_triD4
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g)
    {X : Type} [Group X] [Finite X] (φ : (triD4Universal F σ).K →* X)
    (hker : φ.ker ≤ Subgroup.center (triD4Universal F σ).K)
    {β : Fin (triD4Universal F σ).D.rank → ℤ} (hl : GGLongRoot (triD4Universal F σ).D β)
    (u : (triD4Universal F σ).K) :
    GGRootInnerAt φ.range (ggRootSub (triD4Universal F σ).D φ β u) := by
  have hI := tforms_inner_range hF φ hker hl u
  intro Y hY2 hYK hYR hNY
  refine ggRootNormInner_le_sup_centralizer ?_ hYK hYR hY2 hNY hI
  exact Subgroup.map_le_range _ _

theorem ggRootNoCentralAt_triD4
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g)
    {X : Type} [Group X] [Finite X] (φ : (triD4Universal F σ).K →* X)
    (hker : φ.ker ≤ Subgroup.center (triD4Universal F σ).K)
    {β : Fin (triD4Universal F σ).D.rank → ℤ} (hl : GGLongRoot (triD4Universal F σ).D β)
    (u : (triD4Universal F σ).K) :
    GGRootNoCentralAt φ.range (ggRootSub (triD4Universal F σ).D φ β u) := by
  rcases hF with ⟨hg, hcard, hσ⟩
  have hφker : φ.ker = ⊥ := tforms_ker_eq_bot ⟨hg, hcard, hσ⟩ φ hker
  have hodd : Odd (Nat.card φ.ker) := by
    rw [hφker, Subgroup.card_bot]
    exact odd_one
  have hσ3 : ∀ c : F, σ (σ (σ c)) = c :=
    CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card hcard hσ
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ g * 3) (by rw [hcard, ← pow_mul])
  have hβroot : β ∈ (triD4Universal F σ).D.roots := tforms_GGLongRoot_mem_roots hl
  have hR : IsPGroup 2 (ggRootSub (triD4Universal F σ).D (MonoidHom.id _) β u) := by
    have hR' : IsPGroup 2
        (((triD4Universal F σ).D.rootGroup β).map (MulAut.conj u).toMonoidHom) :=
      (CFSG.SectionRank.isPGroup_twistedRootGroup hσ3 hβroot).map
        (MulAut.conj u).toMonoidHom
    have h1 : ggRootSub (triD4Universal F σ).D (MonoidHom.id _) β u =
        (((triD4Universal F σ).D.rootGroup β).map (MulAut.conj u).toMonoidHom) := by
      simp only [ggRootSub, Subgroup.map_id]
    rw [h1]
    exact hR'
  have hNCC : GGRootNoCentralAt (⊤ : Subgroup (triD4Universal F σ).K)
      (ggRootSub (triD4Universal F σ).D (MonoidHom.id _) β u) := by
    have h1 : ggRootSub (triD4Universal F σ).D (MonoidHom.id _) β u =
        (((triD4Universal F σ).D.rootGroup β).map (MulAut.conj u).toMonoidHom) := by
      simp only [ggRootSub, Subgroup.map_id]
    rw [h1]
    exact ggRootNoCentral_triD4 ⟨hg, hcard, hσ⟩ hl u
  have hmap := CFSG.StandardType.LieKnownR2.SpecialLinearNC.ggRootNoCentralAt_map_of_odd_central_ker
    φ hker hodd hR hNCC
  have heq : (ggRootSub (triD4Universal F σ).D (MonoidHom.id _) β u).map φ =
      ggRootSub (triD4Universal F σ).D φ β u := by
    simp only [ggRootSub, Subgroup.map_id]
  rwa [heq] at hmap

end CFSG.StandardType.LieKnownR2.TriD4

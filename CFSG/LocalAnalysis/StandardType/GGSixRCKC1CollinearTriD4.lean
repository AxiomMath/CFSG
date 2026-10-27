module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearLong
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBTriCore
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongLift
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4BridgeLongRoot
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHNbr
public import CFSG.LieType.HighestRoot.GenModels
public import CFSG.ClassicalInvolution.ModelFacts.Families
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LemmaHTriD4

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

theorem coreFour_triD4_highest
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g) :
    ⁅pCoreOf 2 (Subgroup.normalizer
          ((twistedDatum σ).rootGroup (highRoot .G2) : Set (twistedGroup σ))),
        pCoreOf 2 (Subgroup.normalizer
          ((twistedDatum σ).rootGroup (highRoot .G2) : Set (twistedGroup σ)))⁆ ≤
        (twistedDatum σ).rootGroup (highRoot .G2) ∧
      pCoreOf 2 (Subgroup.normalizer
          ((twistedDatum σ).rootGroup (highRoot .G2) : Set (twistedGroup σ))) ≤
        Subgroup.centralizer
          ((twistedDatum σ).rootGroup (highRoot .G2) : Set (twistedGroup σ)) := by
  have hchar : CharP F 2 := charP_two_of_triField hF
  refine ⟨CFSG.StandardType.RCKK1II.rckTriC_hQ σ hF, ?_⟩
  let σ' : F ≃+* F := RingEquiv.ofBijective σ
    ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ' : σ'.toRingHom = σ := rfl
  let e : twistedGroup σ ≃* graphFixedRootGroup TwistTag.D4 F σ :=
    CFSG.StandardType.LieKnownR2.TriD4.Bridge.triD4BridgeEquiv σ hF.1 hF.2.1 hF.2.2
  have hH : ((twistedDatum σ).rootGroup (highRoot .G2)).map e.toMonoidHom =
      CFSG.StandardType.LieKnownR2.TriD4.Bridge.triD4C0HighRoot F σ :=
    CFSG.StandardType.LieKnownR2.TriD4.Bridge.triD4BridgeEquiv_twistedRootGroup_highRoot
      σ hF.1 hF.2.1 hF.2.2
  have hmap := CFSG.StandardType.LieKnownR2.map_pCoreOf_normalizer_mulEquiv e
    ((twistedDatum σ).rootGroup (highRoot .G2))
  rw [hH] at hmap
  have hC0 := CFSG.StandardType.LieKnownR2.TriD4.Inner.triD4_pCore_le_centralizer
    (K := F) σ'
  rw [hσ'] at hC0
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  apply e.injective
  have hx' : e x ∈ pCoreOf 2 (Subgroup.normalizer
      (CFSG.StandardType.LieKnownR2.TriD4.Bridge.triD4C0HighRoot F σ :
        Set (graphFixedRootGroup TwistTag.D4 F σ))) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hx
  have hy' : e y ∈ CFSG.StandardType.LieKnownR2.TriD4.Bridge.triD4C0HighRoot F σ := by
    rw [← hH]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hy
  have hcomm := Subgroup.mem_centralizer_iff.mp (hC0 hx') (e y) hy'
  simpa only [map_mul] using hcomm

theorem coreFour_triD4_long
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g)
    {β : Fin (Tag.rank .G2) → ℤ} (hl : GGLongRoot (twistedDatum σ) β) (u : twistedGroup σ)
    {Rr Q : Subgroup (twistedGroup σ)}
    (hRr : Rr = ggRootSub (twistedDatum σ) (MonoidHom.id (twistedGroup σ)) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (twistedGroup σ)))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (twistedGroup σ)) := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c :=
    CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card (q := 2 ^ g) hF.2.1 hF.2.2
  have hmax : ∀ γ₀ ∈ (twistedDatum σ).roots,
      (∀ δ ∈ (twistedDatum σ).roots, ht δ ≤ ht γ₀) → γ₀ = highRoot .G2 := by
    intro γ₀ hγ₀ hle
    have hγ₀root : IsRoot .G2 γ₀ :=
      CFSG.LieType.Steinberg.TwistedD4.isRoot_of_mem_twistedDatum_roots σ hγ₀
    have hhigh : highRoot .G2 ∈ (twistedDatum σ).roots := by
      rw [CFSG.LieType.Steinberg.TwistedD4.twistedDatum_roots]
      exact CFSG.SeitzReduction.isRoot_highRoot .G2
    have h1 : ht (highRoot .G2) ≤ ht γ₀ := hle (highRoot .G2) hhigh
    have h2 : ht γ₀ ≤ ht (highRoot .G2) :=
      CFSG.SeitzReduction.height_le_height_highRoot (τ := .G2) hγ₀root
    exact CFSG.StandardType.LieKnownR2.TriD4.Bridge.eq_highRoot_G2_of_height_eq
      hγ₀root (le_antisymm h2 h1)
  exact CFSG.StandardType.LieKnownR2.coreFour_long_of_core
    (CFSG.LieType.Steinberg.TwistedD4.twistedDatum_isCTGroupDatum σ hσ3)
    (r := highRoot .G2)
    (by
      rw [CFSG.LieType.Steinberg.TwistedD4.twistedDatum_roots]
      exact CFSG.SeitzReduction.isRoot_highRoot .G2)
    hmax
    (coreFour_triD4_highest hF) hl u hRr hQ

theorem rckCollinearVia_triD4_long
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hF : TriField F σ g)
    {β : Fin (triD4Universal F σ).D.rank → ℤ} (hl : GGLongRoot (triD4Universal F σ).D β) :
    RCKCollinearVia (triD4Universal F σ) β := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c :=
    CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card (q := 2 ^ g) hF.2.1 hF.2.2
  have hchar : CharP F 2 := charP_two_of_triField hF
  have hfin : Finite (triD4Universal F σ).K := by
    change Finite ↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ)
    infer_instance
  have hβ : β ∈ (triD4Universal F σ).D.roots := by
    have hl' := hl
    obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := hl'
    exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w
  have hX : IsPGroup 2 ((triD4Universal F σ).D.rootGroup β) := by
    change IsPGroup 2 (CFSG.LieType.Steinberg.TwistedD4.twistedRootGroup σ β)
    exact CFSG.LieType.HighestRoot.isPGroup_twistedD4_rootGroup σ hσ3
      (CFSG.LieType.Steinberg.TwistedD4.isRoot_of_mem_twistedDatum_roots σ hβ)
  exact @rckCollinearVia_of_long (triD4Universal F σ) hfin _ _
    (CFSG.LieType.Steinberg.TwistedD4.twistedDatum_isCTGroupDatum σ hσ3)
    (CFSG.LieType.Steinberg.TwistedD4.twistedDatum_steinbergExtras σ hσ3)
    CFSG.ClassicalInvolution.ModelFacts.isIrreducible_G2 rfl
    (rckGL1_centerPPrime_triD4 hF) β hl hX
    (fun u => (coreFour_triD4_long hF hl u rfl rfl).1)

theorem rckCollinearRest_holds :
    RCKCollinearRest :=
  fun _ _ _ _ _ _ hF hl => rckCollinearVia_triD4_long hF hl

end CFSG.StandardType.RCKC1

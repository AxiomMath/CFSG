module

public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
public import CFSG.LocalAnalysis.StandardType.GGFamOuterDFour
public import CFSG.LocalAnalysis.StandardType.GGFamTwoDGraph
public import CFSG.LocalAnalysis.StandardType.GGJ4dKernel24
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3Pair
public import CFSG.LocalAnalysis.StandardType.GGLieCoreSmallSetup
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwoDFourLayer
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw
public import CFSG.CGT.Timmesfeld75.Form2
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26AutMain
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
public import CFSG.LargeExtraspecial.S97RZStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Levi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightChoice
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidSetup
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidTheta
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs141f2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311e2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma138b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterOmegaExc
public import CFSG.Quasithin.Background.G1Basic
public import CFSG.Quasithin.SteinbergCBGDTrace

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.RankThree.PartOne.KD4T
  CFSG.StandardType.TableCRes CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.CrossChar


private theorem u1aO4_ratOrbit_eq_of_image_eq {τ : Tag}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    (h : (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ = Ψ) :
    LieCore.ratOrbit (fun u => ρ u) Ψ = Ψ := by
  have hiter : ∀ k : ℕ, (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' Ψ = Ψ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ', Set.image_comp, ih, h]
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    rw [← hiter k]
    exact Set.mem_image_of_mem _ hδ
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

private theorem u1aO4_mem_ratComp_of_perfect {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (Δ : LangDatum τ GGL) (Ψ : Set (Fin τ.rank → ℤ))
    (hrat : LieCore.ratOrbit (fun u => ρ u) Ψ = Ψ)
    {P : Subgroup (ModGL τ GGL)} (hPle : P ≤ rootSpan τ GGL Ψ ⊓ Δ.model)
    (hPperf : ⁅P, P⁆ = P) {g : ModGL τ GGL} (hgP : g ∈ P) :
    g ∈ LieCore.ratComp ρ Δ.Γ Ψ := by
  have hPGam : P ≤ Δ.Γ := by
    rw [← hPperf]
    exact Subgroup.commutator_mono (hPle.trans inf_le_right) (hPle.trans inf_le_right)
  have hPspan : P ≤ rootSpan τ GGL Ψ := hPle.trans inf_le_left
  have hmain : ⁅P, P⁆ ≤ ⁅rootSpan τ GGL Ψ ⊓ Δ.Γ, rootSpan τ GGL Ψ ⊓ Δ.Γ⁆ :=
    Subgroup.commutator_mono (le_inf hPspan hPGam) (le_inf hPspan hPGam)
  have h1 : g ∈ ⁅P, P⁆ := by
    rw [hPperf]
    exact hgP
  rw [LieCore.ratComp, hrat]
  exact hmain h1

private theorem u1aO4_layer_d4_outer_untwisted {τ : Tag} [E6Sub τ] {p₀ : ℕ}
    (hsearch : D4BaseSearch τ) (hL3 : D4TrialityLayer τ) (hL2 : D4SwapLayer τ)
    (S : LangSetup τ GGL p₀) {Fr : GGL →+* GGL} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) GGL w)
    (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {b : Fin τ.rank → GGLˣ} (j : KernelComponent (rootCharHom b)) (v : WeylGroup τ)
    (hΨeq : componentRoots (rootCharHom b) j =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom b) j, S.ρ γ ∈ componentRoots (rootCharHom b) j)
    (h1 : ¬ twistInner (componentRoots (rootCharHom b) j) (S.ρ : (Fin τ.rank → ℤ) → _)) :
    CFSG.IsQuasisimple ↥(rootSpan τ GGL (componentRoots (rootCharHom b) j) ⊓ S.D.model) := by
  classical
  set Ψ := componentRoots (rootCharHom b) j with hΨdef
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ hγ.1.1]
    exact hρ γ hγ
  have hmaps : MapsJ τ (d4Set τ) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨeq ▸ hw (v • α) (hΨeq ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Nodes τ), w₀ • α = permLattice π α := fun α hα => by
    have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set τ)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
    rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply h1
    refine ⟨v * u * v⁻¹, hΨeq ▸ conj_mem_closure_rootReflection v hu, ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨeq ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    rw [hρw _ hγ.1.1]
    calc w • v • α = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
      _ = v • (u • α) := by
          rw [hact α hα]
          rfl
      _ = (v * u * v⁻¹) • v • α := by
          rw [mul_smul, mul_smul, inv_smul_smul]
  have h12 : e6Idx (τ := τ) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
  have h14 : e6Idx (τ := τ) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have h24 : e6Idx (τ := τ) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
  have hv1 : (e6Idx (τ := τ) 1).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inl rfl
  have hv2 : (e6Idx (τ := τ) 2).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inl rfl)
  have hv4 : (e6Idx (τ := τ) 4).val ∈ ({1, 2, 4} : Set ℕ) := by
    rw [e6Idx_val']; exact Or.inr (Or.inr rfl)
  have hlayer : CFSG.IsQuasisimple ↥(rootSpan τ GGL Ψ ⊓ S.D.model) := by
    rw [hΨeq]
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hπ1
    · exact (rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h12 hv1 hv2 hact).2
    · exact (rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h14 hv1 hv4 hact).2
    · exact (rootSpan_inf_model_quasisimple_d4_swap hL2 S hFr hΦ hn v hu h24 hv2 hv4 hact).2
    · exact (rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h12 h24 h14 hv1 hv2 hv4
        hact).2
    · exact (rootSpan_inf_model_quasisimple_d4 hL3 S hFr hΦ hn v hu h14 h24.symm h12 hv1 hv4 hv2
        hact).2
  exact hlayer

private theorem u1aO4_layer_d4_twE6 {p₀ : ℕ} (S : LangSetup Tag.E6 GGL p₀)
    (hS : ∃ (t : TwistTag) (h : t.tag = .E6) (Fr : GGL →+* GGL), (∀ c, Fr c = c ^ S.D.q) ∧
      ∀ g, S.D.Φ g = diagramAt .E6 GGL t h * Units.map (entrywiseHom Fr) g *
        (diagramAt .E6 GGL t h)⁻¹)
    {b : Fin Tag.E6.rank → GGLˣ} (j : KernelComponent (rootCharHom b)) (v : WeylGroup Tag.E6)
    (hΨeq : componentRoots (rootCharHom b) j =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom b) j, S.ρ γ ∈ componentRoots (rootCharHom b) j)
    (hnin : ¬ twistInner (componentRoots (rootCharHom b) j) (S.ρ : (Fin Tag.E6.rank → ℤ) → _)) :
    CFSG.IsQuasisimple ↥(rootSpan Tag.E6 GGL (componentRoots (rootCharHom b) j) ⊓ S.D.model) :=
  isQuasisimple_rootSpan_inf_model_of_d4_twE6_of_layer S hS j v hΨeq hρ hnin
    (fun ℓ f _ _ hf n hn' u hu π hleaf hπ1 _ hact => by
      have hE6 : E6FixDNAll := e6FixDNAll_proved
      have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
      have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
      have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
      have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
          (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
      have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
          (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
      have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
          (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
      rcases hleaf with hc | hc | hc | hc | hc | hc
      · exact absurd hc hπ1
      · rw [hc] at hact
        exact (twisted_swap_layer_E6 hE6 hf h12 hv1 hv2 hn' hu hact).2
      · rw [hc] at hact
        exact (twisted_swap_layer_E6 hE6 hf h14 hv1 hv4 hn' hu hact).2
      · rw [hc] at hact
        exact (twisted_swap_layer_E6 hE6 hf h24 hv2 hv4 hn' hu hact).2
      · rw [hc] at hact
        exact (twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn' hu hact).2
      · rw [hc] at hact
        exact (twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn' hu hact).2)

private theorem u1aO4_layer_twoD_four {τ : Tag} {p₀ : ℕ} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (S : LangSetup τ GGL p₀) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ι : Type} {a : ι → Fin τ.rank → GGLˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hr : compRank (componentRoots (famCharHom a) i) = 4)
    (hc : (componentRoots (famCharHom a) i).ncard = 24)
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)])) :
    CFSG.IsQuasisimple ↥(rootSpan τ GGL (componentRoots (famCharHom a) i) ⊓ S.D.model) := by
  obtain ⟨b, j, v, hsel, hpin, hρ, hs, hout'⟩ :=
    fam_outerD_four_selected_data hτ S hp hp2 hT hap i hr hc hout
  have hpinb : componentRoots (rootCharHom b) j =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ) := by
    rw [hsel]
    exact hpin
  have hρj : ∀ γ ∈ componentRoots (rootCharHom b) j,
      S.ρ γ ∈ componentRoots (rootCharHom b) j := by
    rw [hsel]
    exact hρ
  have houtj : ¬ twistInner (componentRoots (rootCharHom b) j) (S.ρ : (Fin τ.rank → ℤ) → _) := by
    rw [hsel]
    exact hout'
  have hlayer : CFSG.IsQuasisimple
      ↥(rootSpan τ GGL (componentRoots (rootCharHom b) j) ⊓ S.D.model) := by
    rcases hτ with rfl | rfl | rfl
    · obtain ⟨w, hn⟩ := S.D.n_weyl
      obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
      rcases hP with rfl | ⟨t, ht, rfl⟩
      · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
          ext1 g
          rw [hΦ, one_mul, inv_one, mul_one]
        exact u1aO4_layer_d4_outer_untwisted d4Base_E6 d4TrialityLayer_E6
          (d4SwapLayer_E6 e6FixDNAll_proved) S hFr hΦ' hn
          (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) j v hpinb hρj houtj
      · exact u1aO4_layer_d4_twE6 S ⟨t, ht, Fr, hFr, hΦ⟩ j v hpinb hρj houtj
    · obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
      obtain ⟨w, hn⟩ := S.D.n_weyl
      exact u1aO4_layer_d4_outer_untwisted d4Base_E7
        CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 (d4SwapLayer_E7 e6FixDNAll_proved) S hFr
        hΦ hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) j v hpinb hρj houtj
    · obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
      obtain ⟨w, hn⟩ := S.D.n_weyl
      exact u1aO4_layer_d4_outer_untwisted d4Base_E8
        CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 (d4SwapLayer_E8 e6FixDNAll_proved) S hFr
        hΦ hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) j v hpinb hρj houtj
  rw [hsel] at hlayer
  exact hlayer

private theorem u1aO4_perfect_high {τ : Tag} {p₀ : ℕ} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (S : LangSetup τ GGL p₀) {M : Type} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    {b : Fin τ.rank → GGLˣ} (j : KernelComponent (rootCharHom b))
    (hsel : componentRoots (rootCharHom b) j = componentRoots χ i)
    (hker : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ)
    (hρΨ : ∀ γ ∈ componentRoots χ i, S.ρ γ ∈ componentRoots χ i)
    (h5 : 5 ≤ compRank (componentRoots χ i))
    (hD : (componentRoots χ i).ncard =
      2 * compRank (componentRoots χ i) * (compRank (componentRoots χ i) - 1))
    (hout : ¬ twistInner (componentRoots χ i) (S.ρ : (Fin τ.rank → ℤ) → _)) :
    ∃ P : Subgroup (ModGL τ GGL),
      P ≤ rootSpan τ GGL (componentRoots χ i) ⊓ S.D.model ∧ ⁅P, P⁆ = P ∧
      ∀ g ∈ rootSpan τ GGL (componentRoots χ i) ⊓ S.D.model, g * g = 1 → g ∈ P := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := S.exists_char_pow
  have h2inst : CharP GGL 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) GGL).injective 2
  have hr2 : r = 2 := CharP.eq GGL hchar h2inst
  subst hr2
  haveI : Fact (Nat.Prime 2) := ⟨hr⟩
  haveI : CharP GGL 2 := hchar
  set Ψ := componentRoots χ i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hSC : ∀ T : Set (Fin τ.rank → ℤ),
      torusGroup τ GGL ⊔ rootSpan τ GGL T ≤ adjointGroup τ GGL := fun T =>
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  obtain ⟨v, hv, hmaps, hpos, hG, m, hm, ε, hε⟩ :=
    fam_exists_graphTwist_labelled S χ i hρΨ h5 hD hout
  have hiso := S.iform_rhoTwist v
  have hinj := injective_of_iform _ hiso
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hf : RootAut.IsIsometry Ψ (S.rhoTwist v) :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ' _ => hiso γ δ',
      fun γ _ => map_neg _ γ⟩
  have hΔ : ∀ β ∈ simpleRoots Ψ, S.rhoTwist v β ∈ simpleRoots Ψ := fun β hβ =>
    hf.apply_mem_simpleRoots hΨ hpos hβ
  have hv' : v ∈ componentWeylGroup (componentRoots (rootCharHom b) j) := by
    rw [hsel]
    exact hv
  have hΔ' : ∀ β ∈ simpleRoots (componentRoots (rootCharHom b) j),
      S.rhoTwist v β ∈ simpleRoots (componentRoots (rootCharHom b) j) := by
    intro β hβ
    rw [hsel] at hβ ⊢
    exact hΔ β hβ
  obtain ⟨y, hyZb, hyM, hyv, hpinb⟩ := S.exists_twoD_pin (a := b) hq j hv' hΔ'
  have hyZ : y ∈ torusGroup τ GGL ⊔ rootSpan τ GGL Ψ := hsel ▸ hyZb
  obtain ⟨Q, hQT, hQG, hstep⟩ := S.exists_step_frobTwist_adjoint hq
  have hyC : y ∈ adjointGroup τ GGL := hSC Ψ hyZ
  have hFc : ∀ g, frobTwistGL τ GGL 2 e (y * Q) g = y * S.D.step g * y⁻¹ := by
    intro g
    rw [hstep, frobTwistGL_apply, frobTwistGL_apply]
    group
  have hcT : y * Q ∈ Subgroup.normalizer (torusGroup τ GGL : Set (ModGL τ GGL)) :=
    mul_mem (mem_normalizer_torusGroup_of_mem_monomialSubgroup hyM) hQT
  have hcG : (adjointGroup τ GGL).map (MulAut.conj (y * Q)).toMonoidHom = adjointGroup τ GGL := by
    have e1 : (MulAut.conj (y * Q)).toMonoidHom =
        (MulAut.conj y).toMonoidHom.comp (MulAut.conj Q).toMonoidHom := by
      ext g
      simp [mul_assoc]
    rw [e1, ← Subgroup.map_map, hQG]
    exact CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hyC)
  have hπ : weylQuotientHom τ GGL ⟨y, hyM⟩ = v := weylQuotientHom_eq hyv
  have hU : ∀ γ ∈ componentRoots χ i,
      (rootSubgroup τ GGL γ).map (frobTwistGL τ GGL 2 e (y * Q)) =
        rootSubgroup τ GGL (S.rhoTwist v γ) := by
    intro γ hγ
    have hγr := hΨ.isRoot γ (hΨdef ▸ hγ)
    have e1 : frobTwistGL τ GGL 2 e (y * Q) = (MulAut.conj y).toMonoidHom.comp S.D.step := by
      ext g : 1
      rw [hFc]
      rfl
    rw [e1, ← Subgroup.map_map, S.frob.map_rootSubgroup γ hγr,
      CFSG.RankThree.Lattice.GenFixedRootDatum.map_conj_rootSubgroup_of_mem_monomialSubgroup hyM
        ((S.frob.isRoot_iff γ).2 hγr), hπ]
    rfl
  have hpin' : ∀ β ∈ simpleRoots (componentRoots χ i), ∀ A : SL2 GGL,
      frobTwistGL τ GGL 2 e (y * Q) (rootSL2 τ GGL β A) =
        rootSL2 τ GGL (S.rhoTwist v β)
          (Matrix.SpecialLinearGroup.map (iterateFrobenius GGL 2 e) A) := by
    intro β hβ A
    rw [hFc]
    exact hpinb β (by rw [hsel]; exact hβ) A
  have htor : ∀ t ∈ torusGroup τ GGL, ∃ N : ℕ, Nat.Coprime N 2 ∧ t ^ N = 1 := by
    intro t ht
    obtain ⟨l, rfl⟩ := CFSG.LieType.Chevalley.exists_rootDiagUnit_eq_of_mem_torusGroup ht
    obtain ⟨N, hN, hlN⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j.exists_coprime_pow_eq_one_algClosure
        (K := ZMod 2) Nat.prime_two (ringChar.eq (ZMod 2) 2) l
    refine ⟨N, hN, ?_⟩
    exact
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall
        hlN
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  obtain ⟨C, hCperf, hCle, hCq⟩ :=
    exists_twoD_core_charElem (e := e) hτ' he i (S.rhoTwist v) hiso hmaps hpos hG
      hcT hcG hU hpin' htor
  have hyZ' : y ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots χ) :=
    sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _ hyZ
  obtain ⟨z, hzZ, hz1⟩ := exists_lang_torus_sup_kernelRoots S Nat.one_pos
    (fun γ hγ => by rw [Function.iterate_one]; exact hker γ hγ) hyZ'
  have hz : S.D.step z = z * y := by
    simpa only [iterHom_eq_iterate, Function.iterate_one] using hz1
  have hzC : z ∈ adjointGroup τ GGL := hSC _ hzZ
  have hzN : z ∈ Subgroup.normalizer (rootSpan τ GGL Ψ : Set (ModGL τ GGL)) :=
    Subgroup.mem_normalizer_iff.2 fun g => mem_componentRootSpan_iff_conj_of_mem hzZ i g
  set φ : ModGL τ GGL →* ModGL τ GGL := (MulAut.conj z⁻¹).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj z⁻¹).injective
  have hφapp : ∀ g, φ g = z⁻¹ * g * z := fun g => by rw [hφ]; simp
  set M' : Subgroup (ModGL τ GGL) :=
    adjointGroup τ GGL ⊓ (frobTwistGL τ GGL 2 e (y * Q)).eqLocus (MonoidHom.id _) with hM'
  have hstepz : ∀ g, frobTwistGL τ GGL 2 e (y * Q) (z⁻¹ * g * z) = z⁻¹ * S.D.step g * z := by
    intro g
    rw [hFc, map_mul, map_mul, map_inv, hz]
    group
  have hMap : S.D.model.map φ = M' := by
    ext g
    constructor
    · rintro ⟨x, ⟨hxC, hxF⟩, rfl⟩
      have hxs : S.D.step x = x := hxF
      rw [hφapp]
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hzC) hxC) hzC, ?_⟩
      change frobTwistGL τ GGL 2 e (y * Q) (z⁻¹ * x * z) = z⁻¹ * x * z
      rw [hstepz, hxs]
    · rintro ⟨hgC, hgF⟩
      have hgF' : frobTwistGL τ GGL 2 e (y * Q) g = g := hgF
      refine ⟨z * g * z⁻¹, Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hzC hgC) (inv_mem hzC), ?_⟩, ?_⟩
      · change S.D.step (z * g * z⁻¹) = z * g * z⁻¹
        have h1 := hstepz (z * g * z⁻¹)
        have e2 : z⁻¹ * (z * g * z⁻¹) * z = g := by group
        rw [e2, hgF'] at h1
        calc S.D.step (z * g * z⁻¹) = z * (z⁻¹ * S.D.step (z * g * z⁻¹) * z) * z⁻¹ := by group
          _ = z * g * z⁻¹ := by rw [← h1]
      · rw [hφapp]
        group
  have hspan : (rootSpan τ GGL Ψ).map φ = rootSpan τ GGL Ψ :=
    CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (inv_mem hzN)
  have hPapp : ∀ x, (MulAut.conj z).toMonoidHom x = z * x * z⁻¹ := fun x => rfl
  refine ⟨C.map (MulAut.conj z).toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [hPapp]
    have hxS : x ∈ rootSpan τ GGL Ψ := (hCle hx).1
    have hxM : x ∈ M' := (hCle hx).2
    refine ⟨(Subgroup.mem_normalizer_iff.1 hzN x).1 hxS, ?_⟩
    rw [← hMap] at hxM
    obtain ⟨y', hy', hyx⟩ := hxM
    rw [hφapp] at hyx
    rw [← hyx]
    have e1 : z * (z⁻¹ * y' * z) * z⁻¹ = y' := by group
    rw [e1]
    exact hy'
  · rw [← Subgroup.map_commutator, hCperf]
  · intro g hgM hg2
    have hφg : φ g ∈ rootSpan τ GGL Ψ ⊓ M' := by
      refine ⟨?_, ?_⟩
      · rw [← hspan]
        exact ⟨g, (Subgroup.mem_inf.1 hgM).1, rfl⟩
      · rw [← hMap]
        exact ⟨g, (Subgroup.mem_inf.1 hgM).2, rfl⟩
    have hg2' : g ^ 2 = 1 := by rw [pow_two]; exact hg2
    have hgn : g ^ 2 ^ 1 = 1 := by simpa using hg2'
    have hφgn : φ g ^ 2 ^ 1 = 1 := by rw [← map_pow, hgn, map_one]
    refine ⟨φ g, hCq _ hφg ⟨1, hφgn⟩, ?_⟩
    rw [hPapp, hφapp]
    group

theorem outerTwo_mem_ratComp_typeD {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (Δ : LangDatum τ GGL) (hq : Δ.q = 2) {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap Δ ρ) (hfin : Finite Δ.model) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a₁ a₂ : Fin τ.rank → GGLˣ} (ha₁ : rootDiagUnit τ a₁ ∈ Δ.torus)
    (ha₂ : rootDiagUnit τ a₂ ∈ Δ.torus) (hap₁ : ∀ j, a₁ j ^ p = 1)
    (hap₂ : ∀ j, a₂ j ^ p = 1) (iJ : KernelComponent (LieCore.jointChar a₁ a₂))
    (hb : componentOrbitLength ρ (componentRoots (LieCore.jointChar a₁ a₂) iJ) = 1)
    (houter : ¬ twistInner (componentRoots (LieCore.jointChar a₁ a₂) iJ) ρ)
    (hD : 4 ≤ compRank (componentRoots (LieCore.jointChar a₁ a₂) iJ) ∧
      (componentRoots (LieCore.jointChar a₁ a₂) iJ).ncard =
        2 * compRank (componentRoots (LieCore.jointChar a₁ a₂) iJ) *
          (compRank (componentRoots (LieCore.jointChar a₁ a₂) iJ) - 1))
    {g : ModGL τ GGL}
    (hg : g ∈ rootSpan τ GGL (componentRoots (LieCore.jointChar a₁ a₂) iJ) ⊓ Δ.model)
    (hg2 : g * g = 1) :
    g ∈ LieCore.ratComp ρ Δ.Γ (componentRoots (LieCore.jointChar a₁ a₂) iJ) := by
  classical
  set Ψ : Set (Fin τ.rank → ℤ) := componentRoots (LieCore.jointChar a₁ a₂) iJ with hΨdef
  have hst : (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' Ψ = Ψ :=
    CFSG.StandardType.LangRat.j4d_image_eq_of_componentOrbitLength_eq_one hb
  have hρΨ : ∀ γ ∈ Ψ, ρ γ ∈ Ψ := fun γ hγ => by
    rw [← hst]
    exact ⟨γ, hγ, rfl⟩
  have hrat : LieCore.ratOrbit (fun u => ρ u) Ψ = Ψ := u1aO4_ratOrbit_eq_of_image_eq hst
  obtain ⟨S, hSD, hSρ⟩ :=
    LieCore.exists_langSetup_of_datum Δ ρ hρ hfin le_rfl (by rw [hq, pow_one])
  have hkerJ : ∀ γ ∈ kernelRoots (LieCore.jointChar a₁ a₂),
      ρ γ ∈ kernelRoots (LieCore.jointChar a₁ a₂) := by
    intro γ hγ
    rw [kernelRoots] at hγ ⊢
    refine ⟨(hρ.isRoot_iff γ).2 hγ.1, ?_⟩
    have h1 : rootChar a₁ (ρ γ) = 1 := by
      rw [hρ.rootChar_eq a₁ ha₁ γ hγ.1]
      have h := congrArg Prod.fst hγ.2
      change rootChar a₁ γ = 1 at h
      rw [h, one_pow]
    have h2 : rootChar a₂ (ρ γ) = 1 := by
      rw [hρ.rootChar_eq a₂ ha₂ γ hγ.1]
      have h := congrArg Prod.snd hγ.2
      change rootChar a₂ γ = 1 at h
      rw [h, one_pow]
    show (rootChar a₁ (ρ γ), rootChar a₂ (ρ γ)) = 1
    rw [h1, h2]
    rfl
  have hkerS : ∀ γ ∈ kernelRoots (LieCore.jointChar a₁ a₂),
      S.ρ γ ∈ kernelRoots (LieCore.jointChar a₁ a₂) := by
    intro γ hγ
    simpa only [hSρ] using hkerJ γ hγ
  have hρΨS : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := by
    intro γ hγ
    simpa only [hSρ] using hρΨ γ hγ
  have hs1 : componentOrbitLength S.ρ Ψ = 1 := by
    rw [hSρ]
    exact hb
  have houtS : ¬ twistInner Ψ (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) := by
    simpa only [hSρ] using houter
  obtain ⟨i, hi⟩ := LieCore.exists_famComponent_of_jointChar a₁ a₂ iJ
  have haT : ∀ u : Fin 2,
      rootDiagUnit τ ((![a₁, a₂] : Fin 2 → Fin τ.rank → GGLˣ) u) ∈ S.D.torus := by
    intro u
    rw [hSD]
    fin_cases u
    · simpa using ha₁
    · simpa using ha₂
  have hap : ∀ (u : Fin 2) (j : Fin τ.rank),
      (![a₁, a₂] : Fin 2 → Fin τ.rank → GGLˣ) u j ^ p = 1 := by
    intro u j
    fin_cases u
    · simpa using hap₁ j
    · simpa using hap₂ j
  by_cases h4 : compRank Ψ = 4
  · have hr4 : compRank (componentRoots (famCharHom (![a₁, a₂] : Fin 2 → Fin τ.rank → GGLˣ)) i)
        = 4 := by
      rw [← hi]
      simpa only [hΨdef] using h4
    have hc24 : (componentRoots (famCharHom (![a₁, a₂] : Fin 2 → Fin τ.rank → GGLˣ)) i).ncard
        = 24 := by
      rw [← hi]
      have h24 : Ψ.ncard = 24 := by
        rw [hD.2, h4]
      exact h24
    have houtFam : ¬ twistInner
        (componentRoots (famCharHom (![a₁, a₂] : Fin 2 → Fin τ.rank → GGLˣ)) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (famCharHom (![a₁, a₂] : Fin 2 → Fin τ.rank → GGLˣ)) i)]) := by
      rw [← hi]
      rw [show (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ Ψ] = S.ρ from by
        rw [hs1, Function.iterate_one]]
      exact houtS
    have hlayerFam := u1aO4_layer_twoD_four hτ S hp hp2 haT hap i hr4 hc24 houtFam
    have hlayer : CFSG.IsQuasisimple ↥(rootSpan τ GGL Ψ ⊓ Δ.model) := by
      rw [hΨdef, hi, ← hSD]
      exact hlayerFam
    have hPperf : ⁅(rootSpan τ GGL Ψ ⊓ Δ.model), (rootSpan τ GGL Ψ ⊓ Δ.model)⁆
        = rootSpan τ GGL Ψ ⊓ Δ.model := by
      haveI : Group.IsPerfect ↥(rootSpan τ GGL Ψ ⊓ Δ.model) := hlayer.1
      exact Subgroup.commutator_eq_self
    exact u1aO4_mem_ratComp_of_perfect (P := rootSpan τ GGL Ψ ⊓ Δ.model) Δ Ψ hrat le_rfl
      hPperf hg
  · have h5 : 5 ≤ compRank Ψ := by omega
    obtain ⟨N, b, j, hN, hN2, hbN, hsel⟩ :=
      exists_isolating_element hτ (![a₁, a₂] : Fin 2 → Fin τ.rank → GGLˣ) hp hp2 hap i
    have hkerS' : ∀ γ ∈ kernelRoots (LieCore.jointChar a₁ a₂),
        S.ρ γ ∈ kernelRoots (LieCore.jointChar a₁ a₂) := hkerS
    have hρΨS' : ∀ γ ∈ componentRoots (LieCore.jointChar a₁ a₂) iJ,
        S.ρ γ ∈ componentRoots (LieCore.jointChar a₁ a₂) iJ := hρΨS
    have hD'' : (componentRoots (LieCore.jointChar a₁ a₂) iJ).ncard =
        2 * compRank (componentRoots (LieCore.jointChar a₁ a₂) iJ) *
          (compRank (componentRoots (LieCore.jointChar a₁ a₂) iJ) - 1) := hD.2
    have houtS' : ¬ twistInner (componentRoots (LieCore.jointChar a₁ a₂) iJ)
        (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) := houtS
    have hselJ : componentRoots (rootCharHom b) j =
        componentRoots (LieCore.jointChar a₁ a₂) iJ := by
      rw [hsel, ← hi]
    obtain ⟨P, hPle, hPperf, hPq⟩ :=
      u1aO4_perfect_high (χ := LieCore.jointChar a₁ a₂)
        hτ S iJ j hselJ hkerS' hρΨS' h5 hD'' houtS'
    have hPle' : P ≤ rootSpan τ GGL Ψ ⊓ Δ.model := by
      rw [hΨdef, ← hSD]
      exact hPle
    have hgM : g ∈ rootSpan τ GGL (componentRoots (LieCore.jointChar a₁ a₂) iJ) ⊓ S.D.model := by
      simpa only [hΨdef, hSD] using hg
    exact u1aO4_mem_ratComp_of_perfect (P := P) Δ Ψ hrat hPle' hPperf (hPq g hgM hg2)

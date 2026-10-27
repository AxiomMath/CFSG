module

public import CFSG.LocalAnalysis.StandardType.GGTwE6D4RootFacts
public import CFSG.LocalAnalysis.StandardType.GGTwE6D4GammaLayer
public import CFSG.LocalAnalysis.StandardType.GGTwE6D4E0Data

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType CFSG.StandardType.TableBExc
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffRest
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.KGL
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.StandardType.TwE6EltSmall
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE CFSG.StandardType.LayerSixE
  CFSG.StandardType.LayerExc CFSG.RankThree.PartOne.KE8F
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.KGL.TwLayer
open scoped MatrixGroups commutatorElement

private theorem layer_conj_mem {R : Type} [Group R] {X E : Subgroup R} (h : GGLayerOf X E)
    {g e : R} (hg : g ∈ X) (he : e ∈ E) : g * e * g⁻¹ ∈ E := by
  have h1 := h.2.1.conj_mem ⟨e, h.1 he⟩ (Subgroup.mem_subgroupOf.2 he) ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.1 h1


theorem ggTwE6D4LayerInput_holds : GGTwE6D4LayerInput := by
  intro n hn h3 K _ _ σ hK hσ Fr hFr v hv g0 hg0C hg0 α β hα hβ hαβ ζ hζ hζ1 t ht ta hta ht' hta'
  classical
  haveI : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ hζ1
  have hα' : IsRoot Tag.E6 α := hα
  have hβ' : IsRoot Tag.E6 β := hβ
  have hαβ' : iform (τ := Tag.E6) α β = 0 := hαβ
  set L := AlgebraicClosure K with hL
  obtain ⟨S, hSD⟩ := exists_ennolaSetup_five hn hK hσ (rawTwLang (σ := σ) Fr hFr v g0 hg0C hg0)
  set D := LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr v hg0C hg0 with hD
  have hΓS : S.Γ = D.Γ := by
    show S.D.Γ = D.Γ
    rw [hSD] <;> rfl
  set a : Fin Tag.E6.rank → Lˣ := zetaVec ζ hζ (kgExpVec α + kgExpVec β) with ha
  have hcor : TwE6RootAs.corootTuple α ζ * TwE6RootAs.corootTuple β ζ = a := by
    rw [corootTuple_eq_zetaVec_kg ζ hζ α, corootTuple_eq_zetaVec_kg ζ hζ β]
    exact (CFSG.StandardType.ExcFrames.zetaVec_add ζ hζ _ _).symm
  have hdt : rootDiagUnit Tag.E6 a = twThetaHom g0 t := by
    rw [twThetaHom_apply, ht', hcor] <;> rfl
  have hdα : rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ (kgExpVec α)) = twThetaHom g0 ta := by
    rw [twThetaHom_apply, hta', corootTuple_eq_zetaVec_kg ζ hζ α] <;> rfl
  have hap : ∀ i, a i ^ 3 = 1 := fun i => zetaVec_apply_pow_three hζ _ i
  have h1 : rootDiagUnit Tag.E6 a ≠ 1 :=
    rootDiagUnit_zetaVec_kgExpVec_add_ne_one hζ hζo hα' hαβ'
  have hall : (kernelRoots (rootCharHom a)).ncard = 24 :=
    ncard_kernelRoots_d4 hζo hζ hα' hβ' hαβ'
  have hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -γ := fun γ hγ =>
    ennola_rho_eq_neg (rawTwLang (σ := σ) Fr hFr v g0 hg0C hg0) hv S hSD hγ
  have hT : rootDiagUnit Tag.E6 a ∈ S.D.torus := by
    have hmodel : twThetaHom g0 t ∈ D.model :=
      twThetaHom_mem_model hσ Fr hFr v g0 hg0C hg0 ht
    have htor : twThetaHom g0 t ∈ torusGroup Tag.E6 L := by
      rw [← hdt]
      exact rootDiagUnit_mem_torusGroup a
    rw [hdt, hSD]
    exact mem_twistedTorusOf.2 ⟨htor, (D.mem_model.1 hmodel).2⟩
  obtain ⟨E0, hE0q, hE0Γ, hE0C, hE0n⟩ := a3_E0_data hn hK hσ Fr hFr v hv g0 hg0C hg0
    ζ hζ hζo hα' hβ' hαβ'
  have hE0X : E0 ≤ S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
    rw [hΓS]
    exact le_inf hE0Γ hE0C
  obtain ⟨i, hlayer0⟩ :=
    exists_ggLayerOf_rationalComponent_d4 S hap h1 hT hall hρ ⟨E0, hE0q, hE0X⟩
  obtain ⟨R, hlayerΓ⟩ : ∃ R : Subgroup (ModGL Tag.E6 L),
      GGLayerOf (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a}) R := ⟨_, hlayer0⟩
  have hE0R : E0 ≤ R := hlayerΓ.2.2.2 E0 hE0X (Subgroup.isPerfect_iff.mp hE0q.1)
  obtain ⟨γ, μ, hγ, hμ, hSig, hγα, hμα, hμβ, hμγ⟩ := exists_root_pair_kgL4 hα' hβ' hαβ'
  obtain ⟨hmonoγ, hmapγ⟩ := rootSL2_WSL_monomial_mapsRootLines (L := L) hγ
  obtain ⟨hmonoμ, hmapμ⟩ := rootSL2_WSL_monomial_mapsRootLines (L := L) hμ
  have hΓmem : ∀ δ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 δ → rootSL2 Tag.E6 L δ WSL ∈ S.Γ := by
    intro δ hδ
    rw [hΓS]
    exact rootSL2_WSL_mem_Γ_raw hn hK hσ Fr hFr v hv g0 hg0C hg0 hδ
  have hnγC : rootSL2 Tag.E6 L γ WSL ∈ Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    have hh' : h = rootDiagUnit Tag.E6 a := hh
    rw [hh']
    exact (rootSL2_WSL_commute_rootDiagUnit_zetaVec (L := L) hζ hγ hSig).symm
  obtain ⟨jΓ, hjΓdef⟩ : ∃ jΓ : ModGL Tag.E6 L, jΓ = rootSL2 Tag.E6 L γ WSL *
      rootSL2 Tag.E6 L μ WSL * (rootSL2 Tag.E6 L γ WSL)⁻¹ := ⟨_, rfl⟩
  have hjR : jΓ ∈ R := by
    rw [hjΓdef]
    exact layer_conj_mem hlayerΓ ⟨hΓmem γ hγ, hnγC⟩ (hE0R (hE0n μ hμ hμα hμβ))
  have hmonoj : jΓ ∈ monomialSubgroup Tag.E6 L := by
    rw [hjΓdef]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmonoγ hmonoμ) (Subgroup.inv_mem _ hmonoγ)
  have hmapsj : MapsRootLines jΓ (rootReflection γ * rootReflection μ * (rootReflection γ)⁻¹) := by
    rw [hjΓdef]
    exact (hmapγ.mul hmapμ).mul hmapγ.inv
  set C0 := twistedE6RootGroup K σ with hC0
  let Θ : ↥C0 →* ModGL TwistTag.E6.tag L := (twThetaHom g0).comp C0.subtype
  have hΘinj : Function.Injective Θ :=
    (twThetaHom_injective g0).comp (Subgroup.subtype_injective _)
  have hrange : Θ.range = D.Γ := range_twThetaHom_eq_Γ hn hK hσ Fr hFr v g0 hg0C hg0
  have hmap : ((Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf C0).map Θ =
      S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 a} := by
    rw [hΓS]
    exact map_centralizer_twThetaHom hn hK hσ Fr hFr v g0 hg0C hg0 hdt
  have hlayerC : GGLayerOf
      ((Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf C0) (R.comap Θ) :=
    ggLayerOf_comap Θ hΘinj (by rw [hmap]; exact hlayerΓ)
  have hjΓ' : jΓ ∈ Θ.range := by
    rw [hrange, ← hΓS]
    exact (hlayerΓ.1 hjR).1
  obtain ⟨j, hj⟩ := hjΓ'
  have hΘj : twThetaHom g0 (j : ModGL TwistTag.E6.tag K) = jΓ := hj
  refine ⟨R.comap Θ, hlayerC, j, ?_, ?_, ?_⟩
  · show Θ j ∈ R
    rw [show Θ j = jΓ from hj]
    exact hjR
  · intro x hx
    refine ⟨adAct Tag.E6 3 (rootReflection γ * rootReflection μ * (rootReflection γ)⁻¹) x,
      CFSG.StandardType.NoOffRest.adAct_mem_hypE6 _ hx, ?_⟩
    intro s hs hθ
    have hθ' : twThetaHom g0 s = rootDiagUnit TwistTag.E6.tag (zetaVec ζ hζ x) := by
      rw [twThetaHom_apply]
      exact hθ
    have e : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((j : ModGL TwistTag.E6.tag K) * s * (j : ModGL TwistTag.E6.tag K)⁻¹) * g0 =
        twThetaHom g0 ((j : ModGL TwistTag.E6.tag K) * s * (j : ModGL TwistTag.E6.tag K)⁻¹) :=
      (twThetaHom_apply _ _).symm
    rw [e, map_mul, map_mul, map_inv, hΘj, hθ']
    exact monomial_conj_rootDiagUnit_zetaVec hζ hmonoj hmapsj x
  · intro hconj
    have h2 := congrArg (twThetaHom g0) hconj
    rw [map_mul, map_mul, map_inv, hΘj, ← hdα] at h2
    have h3 : jΓ * rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α)) * jΓ⁻¹ =
        rootDiagUnit Tag.E6 (zetaVec ζ hζ (kgExpVec α)) := h2
    rw [monomial_conj_rootDiagUnit_zetaVec hζ hmonoj hmapsj] at h3
    have h4 := zetaVec_injective hζo hζ (CFSG.LieType.Chevalley.rootDiagUnit_injective h3)
    exact adAct_conj_ne hγ hμ hμα hγα hμγ h4

end CFSG.StandardType.KGL

end

module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterE6
public import CFSG.LocalAnalysis.StandardType.GGFinModelTw
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCTwGen
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.Blueprint.ChevalleyRootGroups
public import CFSG.Blueprint.ChevalleyPinnedLemmas
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.ClassicalInvolution.RouteD.RootCert
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny

theorem rckTw6_hRR
    (h : ℕ) (hh : 1 ≤ h) :
    ⁅twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * h)) (frobQ 2 h),
      twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * h)) (frobQ 2 h)⁆ =
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * h)) (frobQ 2 h) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hh
    (GaloisField 2 (2 * h)) (card_galoisField_two_mul 2 h hh) (frobQ 2 h)
    (frobQ_apply 2 h)).2.2.1

@[expose] noncomputable def rckTw6_psi
    (h : ℕ) (hh : 1 ≤ h) :
    twistedE6Group 2 h →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * h)) (frobQ 2 h)) :=
  (MulEquiv.subgroupCongr (rckTw6_hRR h hh)).toMonoidHom.comp (twistedE6Isogeny 2 h hh)

@[expose] noncomputable def rckTw6_iota
    (h : ℕ) :
    ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * h)) (frobQ 2 h)) →*
      ModGL TwistTag.E6.tag GGL :=
  (baseChangeGL (ggRatEmb (2 * h))).comp
    (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * h)) (frobQ 2 h)).subtype

theorem rckTw6_orbit
    {p₀ : ℕ} (S : LangSetup TwistTag.E6.tag GGL p₀)
    {a : Fin TwistTag.E6.tag.rank → GGLˣ}
    (hT : rootDiagUnit TwistTag.E6.tag a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hn : (componentRoots (rootCharHom a) i).ncard = 72) :
    componentRoots (rootCharHom a) i = {γ | IsRoot TwistTag.E6.tag γ} ∧
      componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
  have hncard : ({γ : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag γ} : Set _).ncard = 72 := by
    have h : ({γ : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag γ} : Set _) =
        ↑(rootFinset TwistTag.E6.tag) := by
      ext α
      simp only [Set.mem_ofPred_eq, Finset.mem_coe]
      exact mem_rootFinset.symm
    rw [h, Set.ncard_coe_finset, card_rootFinset]
    rfl
  have hΨ : componentRoots (rootCharHom a) i = {γ | IsRoot TwistTag.E6.tag γ} := by
    refine Set.eq_of_subset_of_ncard_le (fun γ hγ => isRoot_of_mem_componentRoots hγ) ?_
      (finite_setOf_isRoot TwistTag.E6.tag)
    rw [hncard, hn]
  refine ⟨hΨ, ?_⟩
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  have hstable : (S.ρ : (Fin TwistTag.E6.tag.rank → ℤ) → _)^[1] ''
      componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    rw [Function.iterate_one, hΨ]
    ext v
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      exact (S.frob.isRoot_iff δ).2 hδ
    · intro hv
      refine ⟨S.ρ.symm v, ?_, by simp⟩
      exact (S.frob.isRoot_iff (S.ρ.symm v)).1 (by simpa using hv)
  have hle : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ≤ 1 :=
    Nat.sInf_le ⟨zero_lt_one, hstable⟩
  omega

theorem rckTw6_Phi
    {p₀ : ℕ} (S : LangSetup TwistTag.E6.tag GGL p₀)
    {a : Fin TwistTag.E6.tag.rank → GGLˣ}
    (hT : rootDiagUnit TwistTag.E6.tag a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hΨ : componentRoots (rootCharHom a) i = {γ | IsRoot TwistTag.E6.tag γ})
    (hout1 : ¬ twistInner (componentRoots (rootCharHom a) i) S.ρ)
    {h : ℕ} (hh : 0 < h) (hq : S.D.q = 2 ^ h) :
    S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h) := by
  obtain ⟨Fr, hFr, P, hP, hΦP⟩ := S.D.steinberg
  rcases hP with hP1 | ⟨t, ht, hPt⟩
  · exfalso
    rw [hP1] at hΦP
    simp only [one_mul, inv_one, mul_one] at hΦP
    apply hout1
    obtain ⟨w, hw⟩ := S.D.n_weyl
    have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := MonoidHom.ext hΦP
    refine ⟨w, ?_, fun γ hγ => ?_⟩
    · have hset : {s : WeylGroup TwistTag.E6.tag | ∃ γ ∈ componentRoots (rootCharHom a) i,
          s = rootReflection γ} = {s : WeylGroup TwistTag.E6.tag |
            ∃ γ ∈ ({γ : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag γ} : Set _),
              s = rootReflection γ} := by
        rw [hΨ]
      have htop : Subgroup.closure {s : WeylGroup TwistTag.E6.tag |
          ∃ γ ∈ ({γ : Fin TwistTag.E6.tag.rank → ℤ | IsRoot TwistTag.E6.tag γ} : Set _),
            s = rootReflection γ} = ⊤ := by
        refine top_le_iff.mp ?_
        rw [← closure_range_simple (τ := TwistTag.E6.tag)]
        refine Subgroup.closure_mono ?_
        rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, isRoot_single TwistTag.E6.tag j, ?_⟩
        exact (rootReflection_eq_conj (β := Pi.single j 1) (w := 1) (j := j)
          (by rw [one_smul])).symm
      rw [hset, htop]
      exact Subgroup.mem_top w
    · rw [hΨ] at hγ
      exact S.rho_eq_smul_of_frob hFr hΦ' hw hγ
  · have ht' : t = TwistTag.E6 := by
      cases t
      · rfl
      · exact absurd ht (by decide)
    subst ht'
    have hPdiag : P = diagramMap TwistTag.E6 GGL := by
      rw [hPt]
      cases ht
      rfl
    have hFr_eq : Fr = ggFrobT h := by
      ext c
      rw [hFr c, hq, ggFrobT_apply]
    rw [← hFr_eq]
    refine MonoidHom.ext fun g => ?_
    rw [hΦP, hPdiag]
    rfl

theorem rckTw6_langPkg
    {p₀ : ℕ} (S : LangSetup TwistTag.E6.tag GGL p₀) (h : ℕ) (hf : 1 ≤ h)
    (hΦtw : S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h)) :
    GGLangPkg S.D (rckTw6_iota h) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ggLangPkg_twE6_adjoint hf S.D hΦtw

theorem rckTw6_Gamma
    {p₀ : ℕ} (S : LangSetup TwistTag.E6.tag GGL p₀) (h : ℕ)
    (hΦtw : S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h))
    (hPkg : GGLangPkg S.D (rckTw6_iota h)) :
    S.D.Γ = (show Subgroup (ModGL TwistTag.E6.tag GGL) from (rckTw6_iota h).range).map
      (MulAut.conj S.D.g0⁻¹).toMonoidHom :=
  LangDescent.Γ_eq hPkg.desc

theorem rckTw6_cover_range
    {p₀ : ℕ} (S : LangSetup TwistTag.E6.tag GGL p₀) (h : ℕ) (hf : 1 ≤ h)
    (hΦtw : S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h)) :
    ((MulAut.conj S.D.g0⁻¹).toMonoidHom.comp
      ((rckTw6_iota h).comp (rckTw6_psi h hf))).range = S.D.Γ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPkg : GGLangPkg S.D (rckTw6_iota h) := rckTw6_langPkg S h hf hΦtw
  have hΓ : S.D.Γ = (show Subgroup (ModGL TwistTag.E6.tag GGL) from
      (rckTw6_iota h).range).map (MulAut.conj S.D.g0⁻¹).toMonoidHom :=
    rckTw6_Gamma S h hΦtw hPkg
  have hψ_surj : Function.Surjective (rckTw6_psi h hf) :=
    (MulEquiv.subgroupCongr (rckTw6_hRR h hf)).surjective.comp
      (twistedE6Isogeny_surjective 2 h hf)
  calc ((MulAut.conj S.D.g0⁻¹).toMonoidHom.comp
        ((rckTw6_iota h).comp (rckTw6_psi h hf))).range
      = (((rckTw6_iota h).comp (rckTw6_psi h hf)).range).map
          (MulAut.conj S.D.g0⁻¹).toMonoidHom := by
        exact MonoidHom.range_comp _ _
    _ = (show Subgroup (ModGL TwistTag.E6.tag GGL) from (rckTw6_iota h).range).map
          (MulAut.conj S.D.g0⁻¹).toMonoidHom := by
        rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hψ_surj, Subgroup.map_top]
    _ = S.D.Γ := hΓ.symm

theorem rckTw6_cover_ker
    {p₀ : ℕ} (S : LangSetup TwistTag.E6.tag GGL p₀) (h : ℕ) (hf : 1 ≤ h)
    (hΦtw : S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h)) :
    ((MulAut.conj S.D.g0⁻¹).toMonoidHom.comp
      ((rckTw6_iota h).comp (rckTw6_psi h hf))).ker ≤
        Subgroup.center (twistedE6Group 2 h) := by
  have hPkg : GGLangPkg S.D (rckTw6_iota h) := rckTw6_langPkg S h hf hΦtw
  have hψ_ker_le : (rckTw6_psi h hf).ker ≤ Subgroup.center (twistedE6Group 2 h) := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have h1 : twistedE6Isogeny 2 h hf g = 1 := by
      apply (MulEquiv.subgroupCongr (rckTw6_hRR h hf)).injective
      simpa [rckTw6_psi] using hg
    have h2 : (e6IsogenyT (GaloisField 2 (2 * h)))
        ((fixedGroup (GaloisField 2 (2 * h)) (frobQ 2 h)).subtype g) = 1 := by
      apply Subtype.ext
      have h3 := congrArg (fun y : ↥⁅twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * h))
            (frobQ 2 h), twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * h))
            (frobQ 2 h)⁆ => (y : ModGL TwistTag.E6.tag (GaloisField 2 (2 * h)))) h1
      rw [coe_twistedE6Isogeny] at h3
      simpa using h3
    rw [Subgroup.mem_center_iff]
    intro hh
    exact Subtype.ext (Subgroup.mem_center_iff.1
      (ker_e6IsogenyT_le_center (GaloisField 2 (2 * h)) (MonoidHom.mem_ker.2 h2))
      ((hh : twistedE6Group 2 h) : e6Data_valid.minGroup (GaloisField 2 (2 * h))))
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : ((rckTw6_iota h).comp (rckTw6_psi h hf)) x = 1 := by
    change S.D.g0⁻¹ * (((rckTw6_iota h).comp (rckTw6_psi h hf)) x) * S.D.g0 = 1 at hx
    apply mul_left_cancel (a := S.D.g0⁻¹)
    calc S.D.g0⁻¹ * (((rckTw6_iota h).comp (rckTw6_psi h hf)) x)
        = (S.D.g0⁻¹ * (((rckTw6_iota h).comp (rckTw6_psi h hf)) x) * S.D.g0) * S.D.g0⁻¹ := by
          group
      _ = 1 * S.D.g0⁻¹ := by rw [hx]
      _ = S.D.g0⁻¹ * 1 := by group
  have hxq : x ∈ (rckTw6_psi h hf).ker := by
    rw [MonoidHom.mem_ker]
    exact hPkg.inj (by
      show (rckTw6_iota h) ((rckTw6_psi h hf) x) = (rckTw6_iota h) 1
      rw [show (rckTw6_iota h) ((rckTw6_psi h hf) x) = 1 from hx', map_one])
  exact hψ_ker_le hxq

end CFSG.StandardType.RCKRP

end

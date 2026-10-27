module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover6Aux1

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

theorem rckTw6_hψ_apply
    (h : ℕ) (hh : 1 ≤ h) (g : twistedE6Group 2 h) :
    (rckTw6_iota h) (rckTw6_psi h hh g) =
      ggTwPsi h ((fixedGroup (GaloisField 2 (2 * h)) (frobQ 2 h)).subtype g) := by
  change baseChangeGL (ggRatEmb (2 * h)) ((twistedE6Isogeny 2 h hh g :
      ModGL TwistTag.E6.tag (GaloisField 2 (2 * h)))) =
    ggTwPsi h ((fixedGroup (GaloisField 2 (2 * h)) (frobQ 2 h)).subtype g)
  rw [coe_twistedE6Isogeny]
  rfl

theorem rckTw6_step_lang
    {p₀ : ℕ} (S : LangSetup TwistTag.E6.tag GGL p₀) :
    ∀ g : ModGL TwistTag.E6.tag GGL,
      S.D.step (S.D.g0⁻¹ * g * S.D.g0) = S.D.g0⁻¹ * S.D.Φ g * S.D.g0 := by
  intro g
  show S.D.n * S.D.Φ (S.D.g0⁻¹ * g * S.D.g0) * S.D.n⁻¹ = S.D.g0⁻¹ * S.D.Φ g * S.D.g0
  simp only [map_mul, map_inv, S.D.lang, inv_inv]
  group

theorem rckTw6_Pfix
    :
    ∀ g ∈ rootSpan TwistTag.E6.tag GGL
      ({Pi.single (1 : Fin TwistTag.E6.tag.rank) 1,
        -Pi.single (1 : Fin TwistTag.E6.tag.rank) 1} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      diagramMap TwistTag.E6 GGL * g * (diagramMap TwistTag.E6 GGL)⁻¹ = g := by
  have hgen : ∀ δ ∈ ({Pi.single (1 : Fin TwistTag.E6.tag.rank) 1,
      -Pi.single (1 : Fin TwistTag.E6.tag.rank) 1} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      rootSubgroup TwistTag.E6.tag GGL δ ≤
        Subgroup.centralizer ({diagramMap TwistTag.E6 GGL} :
          Set (ModGL TwistTag.E6.tag GGL)) := by
    intro δ hδ
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
    rw [rootSubgroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    change pinnedX TwistTag.E6.tag GGL δ c ∈ Subgroup.centralizer
      ({diagramMap TwistTag.E6 GGL} : Set (ModGL TwistTag.E6.tag GGL))
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hδ with rfl | rfl
    · rw [pinnedX_single]
      have h2 : diagramMap TwistTag.E6 GGL * xUnit TwistTag.E6.tag GGL 1 c *
          (diagramMap TwistTag.E6 GGL)⁻¹ = xUnit TwistTag.E6.tag GGL 1 c := by
        have h := diagramMap_mul_xUnit_mul_inv (t := TwistTag.E6) (K := GGL) (i := 1) (c := c)
        rw [show (TwistTag.E6.perm) 1 = 1 by decide] at h
        exact h
      calc xUnit TwistTag.E6.tag GGL 1 c * diagramMap TwistTag.E6 GGL
          = (diagramMap TwistTag.E6 GGL * xUnit TwistTag.E6.tag GGL 1 c *
              (diagramMap TwistTag.E6 GGL)⁻¹) * diagramMap TwistTag.E6 GGL := by rw [h2]
        _ = diagramMap TwistTag.E6 GGL * xUnit TwistTag.E6.tag GGL 1 c := by group
    · rw [pinnedX_neg_single]
      have h2 : diagramMap TwistTag.E6 GGL * yUnit TwistTag.E6.tag GGL 1 c *
          (diagramMap TwistTag.E6 GGL)⁻¹ = yUnit TwistTag.E6.tag GGL 1 c := by
        have h := diagramMap_mul_yUnit_mul_inv (t := TwistTag.E6) (K := GGL) (i := 1) (c := c)
        rw [show (TwistTag.E6.perm) 1 = 1 by decide] at h
        exact h
      calc yUnit TwistTag.E6.tag GGL 1 c * diagramMap TwistTag.E6 GGL
          = (diagramMap TwistTag.E6 GGL * yUnit TwistTag.E6.tag GGL 1 c *
              (diagramMap TwistTag.E6 GGL)⁻¹) * diagramMap TwistTag.E6 GGL := by rw [h2]
        _ = diagramMap TwistTag.E6 GGL * yUnit TwistTag.E6.tag GGL 1 c := by group
  intro g hg
  have hle : rootSpan TwistTag.E6.tag GGL
      ({Pi.single (1 : Fin TwistTag.E6.tag.rank) 1,
        -Pi.single (1 : Fin TwistTag.E6.tag.rank) 1} : Set (Fin TwistTag.E6.tag.rank → ℤ)) ≤
      Subgroup.centralizer ({diagramMap TwistTag.E6 GGL} :
        Set (ModGL TwistTag.E6.tag GGL)) := by
    rw [rootSpan]
    exact iSup₂_le (fun δ hδ => hgen δ hδ)
  have hcomm : g * diagramMap TwistTag.E6 GGL = diagramMap TwistTag.E6 GGL * g :=
    Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  calc diagramMap TwistTag.E6 GGL * g * (diagramMap TwistTag.E6 GGL)⁻¹
      = (g * diagramMap TwistTag.E6 GGL) * (diagramMap TwistTag.E6 GGL)⁻¹ := by rw [hcomm]
    _ = g := by group

theorem rckTw6_Phifrob
    {p₀ : ℕ} (S : LangSetup TwistTag.E6.tag GGL p₀) (h : ℕ)
    (hΦtw : S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h)) (σ : GGL ≃+* GGL)
    (hσ : σ.toRingHom = ggFrobT h) :
    ∀ g ∈ rootSpan TwistTag.E6.tag GGL
      ({Pi.single (1 : Fin TwistTag.E6.tag.rank) 1,
        -Pi.single (1 : Fin TwistTag.E6.tag.rank) 1} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      S.D.Φ g = frobGL σ g := by
  intro g hg
  have h1 : S.D.Φ g = diagramMap TwistTag.E6 GGL * frobGL σ g *
      (diagramMap TwistTag.E6 GGL)⁻¹ := by
    rw [hΦtw, ← hσ]
    rfl
  have hPe : frobGL σ (diagramMap TwistTag.E6 GGL) = diagramMap TwistTag.E6 GGL :=
    units_map_entrywiseHom_diagramMap (σ := σ.toRingHom) (t := TwistTag.E6) (K := GGL)
  have hPcomm : diagramMap TwistTag.E6 GGL * frobGL σ g =
      frobGL σ g * diagramMap TwistTag.E6 GGL := by
    calc diagramMap TwistTag.E6 GGL * frobGL σ g
        = frobGL σ (diagramMap TwistTag.E6 GGL) * frobGL σ g := by rw [hPe]
      _ = frobGL σ (diagramMap TwistTag.E6 GGL * g) := by rw [map_mul]
      _ = frobGL σ (g * diagramMap TwistTag.E6 GGL) := by
            congr 1
            calc diagramMap TwistTag.E6 GGL * g
                = diagramMap TwistTag.E6 GGL * g * (diagramMap TwistTag.E6 GGL)⁻¹ *
                    diagramMap TwistTag.E6 GGL := by group
              _ = g * diagramMap TwistTag.E6 GGL := by rw [rckTw6_Pfix g hg]
      _ = frobGL σ g * frobGL σ (diagramMap TwistTag.E6 GGL) := by rw [map_mul]
      _ = frobGL σ g * diagramMap TwistTag.E6 GGL := by rw [hPe]
  rw [h1, hPcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem rckTw6_untwist
    {p₀ : ℕ} (S : LangSetup TwistTag.E6.tag GGL p₀) (h : ℕ)
    (hΦtw : S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h)) (σ : GGL ≃+* GGL)
    (hσ : σ.toRingHom = ggFrobT h) :
    (∀ g : ModGL TwistTag.E6.tag GGL,
      S.D.step (S.D.g0⁻¹ * g * S.D.g0) = S.D.g0⁻¹ * S.D.Φ g * S.D.g0) ∧
    (∀ g ∈ rootSpan TwistTag.E6.tag GGL
      ({Pi.single (1 : Fin TwistTag.E6.tag.rank) 1,
        -Pi.single (1 : Fin TwistTag.E6.tag.rank) 1} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      S.D.step (S.D.g0⁻¹ * g * S.D.g0) = S.D.g0⁻¹ * frobGL σ g * S.D.g0) :=
  ⟨rckTw6_step_lang S,
    fun g hg => by rw [rckTw6_step_lang S g, rckTw6_Phifrob S h hΦtw σ hσ g hg]⟩

theorem rckTw6_pin_of
    (h : ℕ) (hh : 1 ≤ h) (σ : GGL ≃+* GGL) (hσ : ∀ c, σ c = c ^ 2 ^ h)
    (α₀ : Fin TwistTag.E6.tag.rank → ℤ) (β : Fin (Tag.rank .F4) → ℤ)
    (hα₀ : IsRoot TwistTag.E6.tag α₀) (hp : proj α₀ = β) (hfix : rho α₀ = α₀) :
    (twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h) β).map
        ((rckTw6_iota h).comp (rckTw6_psi h hh)) =
      (rootSubgroup TwistTag.E6.tag ↥(fixSubfield σ) α₀).map
        (baseChangeGL (fixSubfield σ).subtype) := by
  apply le_antisymm
  · rintro y ⟨g, hg, rfl⟩
    obtain ⟨c, hc, hgc⟩ :=
      (mem_twistedRootGroup_iff_of_fixed (k := GaloisField 2 (2 * h)) (θ := frobQ 2 h)
        hα₀ hp hfix g).1 hg
    have hval : (rckTw6_iota h) (rckTw6_psi h hh g) =
        pinnedX TwistTag.E6.tag GGL α₀ (ggRatEmb (2 * h) c) := by
      rw [rckTw6_hψ_apply h hh]
      rw [show (fixedGroup (GaloisField 2 (2 * h)) (frobQ 2 h)).subtype g =
        (CFSG.LieType.Steinberg.Minuscule.e6Data_valid).xm
          (GaloisField 2 (2 * h)) α₀ c from hgc]
      exact ggTwPsi_xm h hα₀ c
    rw [show ((rckTw6_iota h).comp (rckTw6_psi h hh)) g =
        pinnedX TwistTag.E6.tag GGL α₀ (ggRatEmb (2 * h) c) from hval]
    have hd : ggRatEmb (2 * h) c ∈ fixSubfield σ := by
      rw [mem_fixSubfield σ, hσ]
      show ggRatEmb (2 * h) c ^ 2 ^ h = ggRatEmb (2 * h) c
      rw [← map_pow, ← frobQ_apply, hc]
    refine Subgroup.mem_map.2 ⟨pinnedX TwistTag.E6.tag ↥(fixSubfield σ) α₀
      ⟨ggRatEmb (2 * h) c, hd⟩, ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨⟨_, hd⟩, rfl⟩
    · rw [baseChangeGL_pinnedX]
      rfl
  · rw [rootSubgroup, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨x, ⟨d, rfl⟩, rfl⟩
    have h1 : (d : GGL) ^ 2 ^ h = d := by
      have h := (mem_fixSubfield σ).1 d.2
      rw [hσ] at h
      exact h
    have hd_pow : (d : GGL) ^ 2 ^ (2 * h) = d := by
      rw [show (2 : ℕ) ^ (2 * h) = 2 ^ h * 2 ^ h by rw [← pow_add]; ring_nf,
        pow_mul, h1, h1]
    obtain ⟨c, hc⟩ :=
      (Set.ext_iff.mp (ggRatEmb_range (f := 2 * h) (by omega)) (d : GGL)).2 hd_pow
    have hcθ : frobQ 2 h c = c := by
      apply (ggRatEmb (2 * h)).injective
      rw [frobQ_apply, map_pow, hc, h1]
    refine ⟨xFixed (frobQ 2 h) hα₀ hfix c hcθ, ?_, ?_⟩
    · exact (mem_twistedRootGroup_iff_of_fixed (k := GaloisField 2 (2 * h)) (θ := frobQ 2 h)
        hα₀ hp hfix (xFixed (frobQ 2 h) hα₀ hfix c hcθ)).2 ⟨c, hcθ, rfl⟩
    · show (rckTw6_iota h) (rckTw6_psi h hh (xFixed (frobQ 2 h) hα₀ hfix c hcθ)) =
          baseChangeGL (fixSubfield σ).subtype (pinnedX TwistTag.E6.tag ↥(fixSubfield σ) α₀ d)
      rw [rckTw6_hψ_apply h hh]
      have e1 : (fixedGroup (GaloisField 2 (2 * h)) (frobQ 2 h)).subtype
          (xFixed (frobQ 2 h) hα₀ hfix c hcθ) =
          (CFSG.LieType.Steinberg.Minuscule.e6Data_valid).xm
            (GaloisField 2 (2 * h)) α₀ c := rfl
      rw [e1]
      exact (ggTwPsi_xm h hα₀ c).trans (by rw [hc, baseChangeGL_pinnedX]; rfl)

theorem rckTw6_perfect
    {p₀ : ℕ} (S : LangSetup TwistTag.E6.tag GGL p₀) (h : ℕ) (hf : 1 ≤ h)
    (hΦtw : S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT h)) :
    ⁅S.Γ, S.Γ⁆ = S.Γ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPkg : GGLangPkg S.D (rckTw6_iota h) := rckTw6_langPkg S h hf hΦtw
  have hΓ : S.D.Γ = (show Subgroup (ModGL TwistTag.E6.tag GGL) from
      (rckTw6_iota h).range).map (MulAut.conj S.D.g0⁻¹).toMonoidHom :=
    rckTw6_Gamma S h hΦtw hPkg
  have hperfC : ⁅graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * h)) (frobQ 2 h),
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * h)) (frobQ 2 h)⁆ =
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * h)) (frobQ 2 h) :=
    (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf
      (GaloisField 2 (2 * h)) (card_galoisField_two_mul 2 h hf) (frobQ 2 h)
      (frobQ_apply 2 h)).1
  have hperfι : ⁅(show Subgroup (ModGL TwistTag.E6.tag GGL) from (rckTw6_iota h).range),
      (show Subgroup (ModGL TwistTag.E6.tag GGL) from (rckTw6_iota h).range)⁆ =
      (show Subgroup (ModGL TwistTag.E6.tag GGL) from (rckTw6_iota h).range) := by
    have hmap : (show Subgroup (ModGL TwistTag.E6.tag GGL) from (rckTw6_iota h).range) =
        (show Subgroup (ModGL TwistTag.E6.tag GGL) from
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * h))
            (frobQ 2 h)).map (baseChangeGL (ggRatEmb (2 * h)))) := by
      change (((baseChangeGL (ggRatEmb (2 * h))).comp
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * h)) (frobQ 2 h)).subtype).range) =
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * h)) (frobQ 2 h)).map
          (baseChangeGL (ggRatEmb (2 * h)))
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hmap, ← Subgroup.map_commutator, hperfC]
  rw [show S.Γ = S.D.Γ from rfl, hΓ, ← Subgroup.map_commutator, hperfι]

theorem rckTw6_cover_all
    {p₀ : ℕ} (S : LangSetup TwistTag.E6.tag GGL p₀)
    {a : Fin TwistTag.E6.tag.rank → GGLˣ}
    (hT : rootDiagUnit TwistTag.E6.tag a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (h6 : compRank (componentRoots (rootCharHom a) i) = 6)
    (hn : (componentRoots (rootCharHom a) i).ncard = 72)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin TwistTag.E6.tag.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    {h : ℕ} (hh : 0 < h) (hq : S.D.q = 2 ^ h) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
      ∃ (φ : twistedE6Group 2 h →* ModGL TwistTag.E6.tag GGL)
        (σ : GGL ≃+* GGL) (z : ModGL TwistTag.E6.tag GGL)
        (γ : Fin TwistTag.E6.tag.rank → ℤ),
        φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        φ.ker ≤ Subgroup.center (twistedE6Group 2 h) ∧
        (∀ c, σ c = c ^ 2 ^ h) ∧
        z ∈ rootSpan TwistTag.E6.tag GGL (componentRoots (rootCharHom a) i) ∧
        φ.range ≤ rootSpan TwistTag.E6.tag GGL (componentRoots (rootCharHom a) i) ∧
        IsRoot TwistTag.E6.tag γ ∧
        γ ∈ componentRoots (rootCharHom a) i ∧ -γ ∈ componentRoots (rootCharHom a) i ∧
        (∀ g ∈ rootSpan TwistTag.E6.tag GGL
          ({γ, -γ} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
          S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) ∧
        ((twistedE6Datum 2 h).rootGroup (Pi.single (0 : Fin 4) 1)).map φ =
          ((rootSubgroup TwistTag.E6.tag ↥(fixSubfield σ) γ).map
            (baseChangeGL (fixSubfield σ).subtype)).map (MulAut.conj z).toMonoidHom ∧
        ((twistedE6Datum 2 h).rootGroup (-Pi.single (0 : Fin 4) 1)).map φ =
          ((rootSubgroup TwistTag.E6.tag ↥(fixSubfield σ) (-γ)).map
            (baseChangeGL (fixSubfield σ).subtype)).map (MulAut.conj z).toMonoidHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ h := hh
  obtain ⟨hΨ, hs1⟩ := rckTw6_orbit S hT i hn
  have hout1 : ¬ twistInner (componentRoots (rootCharHom a) i) S.ρ := by
    rw [hs1, Function.iterate_one] at hout
    exact hout
  have hΦtw := rckTw6_Phi S hT i hΨ hout1 hh hq
  have hPkg : GGLangPkg S.D (rckTw6_iota h) := rckTw6_langPkg S h hf hΦtw
  let z : ModGL TwistTag.E6.tag GGL := S.D.g0⁻¹
  have hz_def : z = S.D.g0⁻¹ := rfl
  let σ : GGL ≃+* GGL := by
    refine RingEquiv.ofBijective (ggFrobT h) ⟨(iterateFrobenius GGL 2 h).injective, ?_⟩
    intro c
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq c (pow_pos (by norm_num : (0 : ℕ) < 2) h)
    exact ⟨y, by rw [ggFrobT_apply, hy]⟩
  have hσ : ∀ c, σ c = c ^ 2 ^ h := fun c => ggFrobT_apply h c
  have hσ' : σ.toRingHom = ggFrobT h := rfl
  let φ : twistedE6Group 2 h →* ModGL TwistTag.E6.tag GGL :=
    (MulAut.conj z).toMonoidHom.comp ((rckTw6_iota h).comp (rckTw6_psi h hf))
  have hφ_def : φ = (MulAut.conj z).toMonoidHom.comp
      ((rckTw6_iota h).comp (rckTw6_psi h hf)) := rfl
  have hrangeφ : φ.range = S.D.Γ := by
    rw [hφ_def, hz_def]
    exact rckTw6_cover_range S h hf hΦtw
  have hkerφ : φ.ker ≤ Subgroup.center (twistedE6Group 2 h) := by
    rw [hφ_def, hz_def]
    exact rckTw6_cover_ker S h hf hΦtw
  have huntwist := rckTw6_untwist S h hΦtw σ hσ'
  have hstep_frob : ∀ g ∈ rootSpan TwistTag.E6.tag GGL
      ({Pi.single (1 : Fin TwistTag.E6.tag.rank) 1,
        -Pi.single (1 : Fin TwistTag.E6.tag.rank) 1} : Set (Fin TwistTag.E6.tag.rank → ℤ)),
      S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
    intro g hg
    rw [hz_def]
    simpa only [inv_inv] using huntwist.2 g hg
  have hzadj : z ∈ adjointGroup TwistTag.E6.tag GGL := by
    rw [hz_def]
    exact (adjointGroup TwistTag.E6.tag GGL).inv_mem S.D.g0_mem
  have hγroot : IsRoot TwistTag.E6.tag (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) :=
    isRoot_single TwistTag.E6.tag 1
  have hprojγ : proj (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) = Pi.single (0 : Fin 4) 1 :=
    (proj_single (1 : Fin TwistTag.E6.tag.rank)).trans rfl
  have hrhoγ : rho (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) =
      Pi.single (1 : Fin TwistTag.E6.tag.rank) 1 :=
    (rho_single (1 : Fin TwistTag.E6.tag.rank)).trans
      (by
        change Pi.single ((TwistTag.E6.perm) 1) 1 = Pi.single 1 1
        rw [show (TwistTag.E6.perm) 1 = 1 by decide]
        rfl)
  have hγproj : proj (-Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) = -Pi.single (0 : Fin 4) 1 :=
    (proj.map_neg (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1)).trans (by rw [hprojγ]; rfl)
  have hrhoneg : rho (-Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) =
      -Pi.single (1 : Fin TwistTag.E6.tag.rank) 1 := by
    rw [show rho (-Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) =
      -rho (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) from rfl, hrhoγ]
    rfl
  have hpin_core := rckTw6_pin_of h hf σ hσ (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1)
    (Pi.single (0 : Fin 4) 1) hγroot hprojγ hrhoγ
  have hpin_core_neg := rckTw6_pin_of h hf σ hσ
    (-Pi.single (1 : Fin TwistTag.E6.tag.rank) 1) (-Pi.single (0 : Fin 4) 1)
    (IsRoot.neg hγroot) hγproj hrhoneg
  have hmap_pin : ∀ β : Fin (Tag.rank .F4) → ℤ,
      (twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h) β).map φ =
        ((twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h) β).map
          ((rckTw6_iota h).comp (rckTw6_psi h hf))).map (MulAut.conj z).toMonoidHom := by
    intro β
    rw [hφ_def]
    exact (Subgroup.map_map (twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h) β)
      (MulAut.conj z).toMonoidHom ((rckTw6_iota h).comp (rckTw6_psi h hf))).symm
  have hstabρ : ∀ δ ∈ componentRoots (rootCharHom a) i,
      S.ρ δ ∈ componentRoots (rootCharHom a) i := by
    intro δ hδ
    rw [hΨ] at hδ ⊢
    exact (S.frob.isRoot_iff δ).2 hδ
  have hratroots : rationalRoots S.ρ (rootCharHom a) i =
      componentRoots (rootCharHom a) i := by
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      induction k with
      | zero => simpa using hδ
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hstabρ _ ih
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
  have hperfΓ := rckTw6_perfect S h hf hΦtw
  have hratComponent : rationalComponent S.ρ S.Γ (rootCharHom a) i = S.D.Γ := by
    unfold rationalComponent rationalSpan
    rw [hratroots, hΨ, ← adjointGroup_eq_rootSpan]
    have hle : S.Γ ≤ adjointGroup TwistTag.E6.tag GGL :=
      le_trans (LangDescent.Γ_le_model hPkg.desc) inf_le_left
    rw [show adjointGroup TwistTag.E6.tag GGL ⊓ S.Γ = S.Γ from inf_eq_right.mpr hle, hperfΓ]
    rfl
  have hzspan : z ∈ rootSpan TwistTag.E6.tag GGL (componentRoots (rootCharHom a) i) := by
    rw [hΨ, ← adjointGroup_eq_rootSpan]
    exact hzadj
  have hφspan : φ.range ≤ rootSpan TwistTag.E6.tag GGL (componentRoots (rootCharHom a) i) := by
    rw [hΨ, ← adjointGroup_eq_rootSpan, hrangeφ]
    exact le_trans (LangDescent.Γ_le_model hPkg.desc) inf_le_left
  refine ⟨hs1, φ, σ, z, Pi.single (1 : Fin TwistTag.E6.tag.rank) 1,
    ?_, hkerφ, hσ, hzspan, hφspan, hγroot, ?_, ?_, hstep_frob, ?_, ?_⟩
  · rw [hrangeφ, ← hratComponent]
  · rw [hΨ]
    exact isRoot_single TwistTag.E6.tag 1
  · rw [hΨ]
    exact IsRoot.neg (isRoot_single TwistTag.E6.tag 1)
  · rw [show (twistedE6Datum 2 h).rootGroup (Pi.single (0 : Fin 4) 1) =
        twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h) (Pi.single (0 : Fin 4) 1) from rfl]
    rw [hmap_pin (Pi.single (0 : Fin 4) 1), hpin_core]
  · rw [show (twistedE6Datum 2 h).rootGroup (-Pi.single (0 : Fin 4) 1) =
        twistedRootGroup (GaloisField 2 (2 * h)) (frobQ 2 h) (-Pi.single (0 : Fin 4) 1) from rfl]
    rw [hmap_pin (-Pi.single (0 : Fin 4) 1), hpin_core_neg]

end CFSG.StandardType.RCKRP

end

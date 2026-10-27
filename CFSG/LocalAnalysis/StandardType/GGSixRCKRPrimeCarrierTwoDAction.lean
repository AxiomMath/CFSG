module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourE8Main
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RootSpanMap
public import CFSG.LocalAnalysis.StandardType.GGRootDetectCore
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SuN

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.StandardType
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.GLTheoremA.T171Sh
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement


theorem rckTwoD_torus_conj_inner
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .twoD)
    {b : ModGL τ L} (hb : b ∈ S.D.torus) :
    ∃ r ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
        b * x * b⁻¹ = r * x * r⁻¹ := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  let s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  haveI : NeZero s := ⟨hs0.ne'⟩
  let P := outerOrbitFamily S hT i hs hmin
  let H := rootSpan τ L (componentRoots (rootCharHom a) i)
  let F : ModGL τ L →* ModGL τ L := iterHom S.D.step s
  have hP0 : P.S 0 = H := by
    rw [outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
    rfl
  have hZ : Subgroup.center H = ⊥ := center_eq_bot_of_twistKind_twoD S hT i hk
  have hperf := twoDExcFixedPointsPerfect_holds S hT i hk
  let d := twoDExcFixedData_of_perfect hperf
  have hFmap : H.map F = H := by
    rw [S.frob.map_rootSpan_iterHom _ (fun γ hγ => isRoot_of_mem_componentRoots hγ) s, hs]
  have hFmem : ∀ x ∈ H, F x ∈ H := fun x hx => by
    rw [← hFmap]
    exact Subgroup.mem_map_of_mem F hx
  have hFsurj : ∀ x ∈ H, ∃ x' ∈ H, F x' = x := fun x hx => by
    rw [← hFmap] at hx
    exact hx
  have hZA : P.Z ≤ Subgroup.centralizer (H : Set (ModGL τ L)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact P.mem_Z.1 hz x (P.S_le_A 0 (by rw [hP0]; exact hx))
  let θ : ↥d.C →* ModGL τ L := d.C.subtype
  have hθS0 : ∀ c, θ c ∈ P.S 0 := fun c => by rw [hP0]; exact d.le c.2
  have hθfix : ∀ c, iterHom S.D.step s (θ c) = θ c := fun c => d.fix c c.2
  have hθY : ∀ g g' : ModGL τ L, g ∈ H → g' ∈ H →
      F g * g⁻¹ ∈ P.Z → F g' * g'⁻¹ ∈ P.Z → ⁅g, g'⁆ ∈ θ.range := by
    intro g g' hg hg' hzg hzg'
    have h := commutator_mem_of_twist_mem_centralizer hZ hFmem hZA d.full hg hg' hzg hzg'
    simpa only [θ, Subgroup.range_subtype] using h
  have hθZ : ∀ c : ↥d.C, θ c ∈ P.Z → c ∈ Subgroup.center ↥d.C := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro c'
    apply Subtype.ext
    exact P.mem_Z.1 hc c' (P.S_le_A 0 (by rw [hP0]; exact d.le c'.2))
  obtain ⟨f, hRlower, -, hRupper, hformula⟩ := rckCov_rationalComponent_eq_range_of_hom_T
    S hT i hs hmin θ hθS0 hθfix hθY hθZ
  have hfrange : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hRupper d.perf) hRlower
  have hbH : b ∈ torusGroup τ L := hb.1
  have hbF : S.D.step b = b := (S.D.mem_model.1 (S.D.torus_le_model hb)).2
  have hbZ : b ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    (le_sup_left : torusGroup τ L ≤ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))) hbH
  obtain ⟨g, hgH, hgconj⟩ := exists_mem_rootSpan_conj_eq_of_mem_Z i hbZ
  change g ∈ rootSpan τ L (unionRoots (rootCharHom a) ({i} : Set (KernelComponent _))) at hgH
  rw [unionRoots_singleton] at hgH
  have hFg : F g = g := iterHom_step_fixed_of_center_eq_bot i hZ F
    (iterHom_eq_self_of_fixed hbF s) hFmem hFsurj hgH hgconj
  let u : ↥d.C := ⟨g, d.full g hgH hFg⟩
  let θ₀ : ↥d.C →* P.S 0 := θ.codRestrict (P.S 0) hθS0
  refine ⟨f u, hfrange ▸ MonoidHom.mem_range.mpr ⟨u, rfl⟩, ?_⟩
  intro x hx
  obtain ⟨c, rfl⟩ := hRlower hx
  have hconj : ((θ₀ (u * c * u⁻¹) : P.S 0) : ModGL τ L) =
      b * (θ₀ c : ModGL τ L) * b⁻¹ := (hgconj c (d.le c.2)).symm
  have hnorm := cycFamily_norm_conj P hbF hconj
  calc b * f c * b⁻¹ = b * P.norm (θ₀ c) * b⁻¹ := by rw [hformula c]
    _ = P.norm (θ₀ (u * c * u⁻¹)) := hnorm.symm
    _ = f (u * c * u⁻¹) := (hformula _).symm
    _ = f u * f c * (f u)⁻¹ := by rw [map_mul, map_mul, map_inv]

theorem rckTwoD_innerDiag_of_range
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .twoD)
    {U : Type*} [Group U] (Δ : UniversalRootDatum U) (φ : U →* ModGL τ L)
    (hφ : φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i)
    {b : ModGL τ L} (hb : b ∈ S.D.torus) : GGPsiInnerDiag Δ φ b := by
  obtain ⟨r, hr, hconj⟩ := rckTwoD_torus_conj_inner S hT i hk hb
  have hrange : r ∈ φ.range := by rw [hφ]; exact hr
  obtain ⟨u, hu⟩ := hrange
  apply RootDetect.ggPsiInnerDiag_of_centralizes (a := u⁻¹) Δ
  intro y
  have hy : φ y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    hφ ▸ MonoidHom.mem_range.mpr ⟨y, rfl⟩
  have h : b * (r⁻¹ * φ y * r) * b⁻¹ = φ y :=
    (hconj _ (mul_mem (mul_mem (inv_mem hr) hy) hr)).trans (by group)
  have hinv : b⁻¹ * φ y * b = r⁻¹ * φ y * r := by
    calc b⁻¹ * φ y * b = b⁻¹ * (b * (r⁻¹ * φ y * r) * b⁻¹) * b := by rw [h]
      _ = r⁻¹ * φ y * r := by group
  rw [map_inv, hu]
  calc (b * r⁻¹)⁻¹ * φ y * (b * r⁻¹) = r * (b⁻¹ * φ y * b) * r⁻¹ := by group
    _ = r * (r⁻¹ * φ y * r) * r⁻¹ := by rw [hinv]
    _ = φ y := by group

end CFSG.StandardType.RCKRP

module

public import CFSG.LocalAnalysis.StandardType.GGFamTameLang
public import CFSG.LocalAnalysis.StandardType.GGFamTameOrbit
public import CFSG.LocalAnalysis.StandardType.GGFamTameTransfer
public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighAssembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighPin
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwoDHighDefs

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped commutatorElement

theorem famTwoDHigh_compRank_eq_finrank_span {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (hΨ : Ψ.Finite) :
    Module.finrank ℤ (Submodule.span ℤ Ψ) = compRank Ψ := by
  let g : (Fin τ.rank → ℤ) → (Fin τ.rank → ℚ) := fun v i => (v i : ℚ)
  let f : (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℚ) :=
    { toFun := g
      map_add' := by intro a b; funext i; simp [g]
      map_smul' := by intro a b; funext i; simp [g] }
  have hfinj : Function.Injective f := by
    intro a b h
    funext i
    have h' := congrFun h i
    exact Int.cast_injective h'
  have : Module.Finite ℤ (Submodule.span ℤ (f '' Ψ)) :=
    Module.Finite.span_of_finite ℤ (hΨ.image f)
  have hmap : (Submodule.span ℤ Ψ).map f = Submodule.span ℤ (f '' Ψ) := by
    rw [Submodule.map_span]
  have heq : Module.finrank ℤ (Submodule.span ℤ Ψ) =
      Module.finrank ℤ (Submodule.span ℤ (f '' Ψ)) := by
    rw [← hmap]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hfinj (Submodule.span ℤ Ψ))
  have hM : Module.finrank ℚ (Submodule.span ℚ (f '' Ψ)) =
      Module.finrank ℤ (Submodule.span ℤ (f '' Ψ)) :=
    Submodule.finrank_span_eq_finrank_span ℤ ℚ (f '' Ψ)
  have hcomp : compRank Ψ = Module.finrank ℚ (Submodule.span ℚ (f '' Ψ)) := by
    rw [compRank]
    rfl
  rw [hcomp, hM]
  exact heq

theorem famTwoDHigh_finite_of_isRootComponent
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) : Ψ.Finite :=
  (CFSG.Blueprint.Chevalley.finite_setOf_isRoot (τ := τ)).subset
    (fun α hα => hΨ.isRoot α hα)

theorem famTwoDHigh_rationalRootsM_eq_of_image_eq {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (hst : (ρ : (Fin τ.rank → ℤ) → _) '' componentRoots χ i = componentRoots χ i) :
    rationalRootsM ρ χ i = componentRoots χ i := by
  have hmem : ∀ γ ∈ componentRoots χ i, ρ γ ∈ componentRoots χ i := fun γ hγ => by
    rw [← hst]
    exact ⟨γ, hγ, rfl⟩
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    induction k generalizing δ with
    | zero => exact hδ
    | succ k ih =>
      rw [Function.iterate_succ_apply]
      exact ih _ (hmem δ hδ)
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

theorem famTwoDHigh_image_componentRoots_eq_of_rank_gt_half
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (hr : τ.rank < 2 * compRank (componentRoots χ i)) :
    S.ρ '' componentRoots χ i = componentRoots χ i := by
  classical
  set Ψ := componentRoots χ i with hΨdef
  obtain ⟨j, hj⟩ := exists_image_component_of_stable (ρ := S.ρ) χ hρ S.frob.iform_eq i
  by_cases hij : i = j
  · subst hij
    rw [hΨdef]
    exact hj
  exfalso
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hJ : IsRootComponent (componentRoots χ j) := isRootComponent_componentRoots j
  have hfin : Ψ.Finite := famTwoDHigh_finite_of_isRootComponent hΨ
  have hfinJ : (componentRoots χ j).Finite := famTwoDHigh_finite_of_isRootComponent hJ
  have horth : ∀ u ∈ Submodule.span ℤ Ψ, ∀ v ∈ Submodule.span ℤ (componentRoots χ j),
      iform u v = 0 := fun u hu v hv =>
    iform_eq_zero_of_mem_span
      (fun x hx y hy => iform_eq_zero_of_mem_componentRoots' hij hx hy) hu hv
  have hrank := finrank_add_finrank_le_of_orth horth
  have hbΨ : Module.finrank ℤ (Submodule.span ℤ Ψ) = compRank Ψ :=
    famTwoDHigh_compRank_eq_finrank_span Ψ hfin
  have hbJ : Module.finrank ℤ (Submodule.span ℤ (componentRoots χ j)) =
      compRank (componentRoots χ j) := famTwoDHigh_compRank_eq_finrank_span _ hfinJ
  have hΛ : Submodule.span ℤ (componentRoots χ j) =
      Submodule.map (rhoLinMap S) (Submodule.span ℤ Ψ) := by
    rw [← hj, Submodule.map_span]
    rfl
  have hfrJ : Module.finrank ℤ (Submodule.span ℤ (componentRoots χ j)) =
      Module.finrank ℤ (Submodule.span ℤ Ψ) := by
    rw [hΛ]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (fun x y hxy => S.ρ.injective hxy) _)).symm
  have hcJ : compRank (componentRoots χ j) = compRank Ψ := by
    rw [← hbJ, ← hbΨ]
    exact hfrJ
  rw [hbΨ, hbJ, hcJ] at hrank
  omega

theorem famTwoDHigh_mem_normalizer_rootSpan_of_mem_Z
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {z : ModGL τ L}
    (hz : z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ))
    (j : KernelComponent χ) :
    z ∈ Subgroup.normalizer
      (rootSpan τ L (componentRoots χ j) : Set (ModGL τ L)) :=
  Subgroup.mem_normalizer_iff.2 (mem_componentRootSpan_iff_conj_of_mem hz j)

theorem famTwoDHigh_exists_isGraphTwist
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (hkind : twistKindM S.ρ χ i = .twoD)
    (h5 : 5 ≤ compRank (componentRoots χ i)) :
    ∃ v ∈ componentWeylGroup (componentRoots χ i),
      (∀ γ ∈ componentRoots χ i, S.rhoTwist v γ ∈ componentRoots χ i) ∧
      (∀ γ ∈ posRoots (componentRoots χ i), S.rhoTwist v γ ∈ posRoots (componentRoots χ i)) ∧
      IsGraphTwist (componentRoots χ i) (S.rhoTwist v) := by
  classical
  set Ψ := componentRoots χ i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  obtain ⟨hni0, h4, hcard⟩ := twistKindM_twoD_unpack S.ρ hkind
  have hr : τ.rank < 2 * compRank Ψ := by
    have h8 := CFSG.HardMathSupport.Timmesfeld.RootAut.rank_le_eight τ
    omega
  have hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' Ψ = Ψ :=
    famTwoDHigh_image_componentRoots_eq_of_rank_gt_half S hρ i hr
  have horb1 : componentOrbitLength S.ρ Ψ = 1 := by
    have h1 : (1 : ℕ) ∈ {s : ℕ | 0 < s ∧ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ} :=
      ⟨Nat.one_pos, by rw [Function.iterate_one]; exact hst⟩
    exact le_antisymm (Nat.sInf_le h1) (Nat.sInf_mem ⟨1, h1⟩).1
  have hni : ¬ twistInner Ψ S.ρ := by
    rw [horb1] at hni0
    simpa using hni0
  have hρΨ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ := fun γ hγ => by
    rw [← hst]
    exact ⟨γ, hγ, rfl⟩
  have hρsΨ : ∀ γ ∈ Ψ, S.ρ.symm γ ∈ Ψ := fun γ hγ => by
    rw [← hst] at hγ
    obtain ⟨δ, hδ, rfl⟩ := hγ
    rwa [Equiv.symm_apply_apply]
  have hfin : Ψ.Finite := famTwoDHigh_finite_of_isRootComponent hΨ
  have hf : IsIsometry Ψ S.ρ.symm := by
    refine ⟨⟨hρsΨ, S.ρ.symm.injective.injOn, fun γ hγ => ⟨S.ρ γ, hρΨ γ hγ,
      S.ρ.symm_apply_apply γ⟩⟩, fun γ _ δ _ => ?_, fun γ _ => ?_⟩
    · have h := iform_rho S (S.ρ.symm γ) (S.ρ.symm δ)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact h.symm
    · apply S.ρ.injective
      rw [Equiv.apply_symm_apply, S.frob.neg_eq, Equiv.apply_symm_apply]
  obtain ⟨u, hu, hpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hf
  have hg := hf.comp_smul hΨ hu
  have hv : u⁻¹ ∈ componentWeylGroup Ψ := inv_mem hu
  have hδg : ∀ γ, S.rhoTwist u⁻¹ (S.ρ.symm (u • γ)) = γ := fun γ => by
    rw [S.rhoTwist_apply, Equiv.apply_symm_apply, inv_smul_smul]
  have hmaps : ∀ γ ∈ Ψ, S.rhoTwist u⁻¹ γ ∈ Ψ := fun γ hγ =>
    smul_mem_of_mem_componentWeylGroup hΨ hv _ (hρΨ γ hγ)
  have hposδ : ∀ γ ∈ posRoots Ψ, S.rhoTwist u⁻¹ γ ∈ posRoots Ψ := by
    intro γ hγ
    obtain ⟨b, hb, rfl⟩ := hg.exists_posRoots hΨ hpos hγ
    rw [hδg]
    exact hb
  have hiso := S.iform_rhoTwist u⁻¹
  have hinj := injective_of_iform _ hiso
  have hfδ : IsIsometry Ψ (S.rhoTwist u⁻¹) :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ _ => hiso γ δ,
      fun γ _ => map_neg _ γ⟩
  have hne : ∃ β ∈ simpleRoots Ψ, S.rhoTwist u⁻¹ β ≠ β := by
    by_contra h
    push Not at h
    apply hni
    refine ⟨u, componentWeylGroup_le Ψ hu, fun γ hγ => ?_⟩
    have h1 := hfδ.eq_self_of_simpleRoots hΨ h hγ
    rw [S.rhoTwist_apply] at h1
    calc S.ρ γ = u • (u⁻¹ • S.ρ γ) := by rw [smul_inv_smul]
      _ = u • γ := by rw [h1]
  have hτ := simplyLaced_of_five_le_rank (le_trans h5 (compRank_le Ψ))
  have hsl : ∀ β ∈ Ψ, iform β β = 2 := fun β hβ => by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ (hΨ.isRoot β hβ)
  exact ⟨u⁻¹, hv, hmaps, hposδ,
    isGraphTwist_of_twoD hΨ hsl h5 hcard _ hiso hmaps hposδ hne⟩

theorem famTwoDHigh_isQuasisimple_rationalComponentM
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    (hst : (S.ρ : (Fin τ.rank → ℤ) → _) '' componentRoots χ i = componentRoots χ i)
    {r e : ℕ} [Fact r.Prime] [CharP L r] (hq : S.D.q = r ^ e) (he : 1 ≤ e)
    {v : WeylGroup τ}
    (hmaps : ∀ γ ∈ componentRoots χ i, S.rhoTwist v γ ∈ componentRoots χ i)
    (hpos : ∀ γ ∈ posRoots (componentRoots χ i), S.rhoTwist v γ ∈ posRoots (componentRoots χ i))
    (hG : IsGraphTwist (componentRoots χ i) (S.rhoTwist v))
    {y : ModGL τ L} (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (componentRoots χ i))
    (hyM : y ∈ monomialSubgroup τ L) (hyv : MapsRootLines y v)
    (hpin : ∀ β ∈ simpleRoots (componentRoots χ i), ∀ A : SL2 L,
      y * S.D.step (rootSL2 τ L β A) * y⁻¹ =
        rootSL2 τ L (S.rhoTwist v β) (Matrix.SpecialLinearGroup.map (iterateFrobenius L r e) A)) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ χ i) := by
  classical
  set Ψ := componentRoots χ i with hΨdef
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hSC : ∀ T : Set (Fin τ.rank → ℤ), torusGroup τ L ⊔ rootSpan τ L T ≤ adjointGroup τ L :=
    fun T => sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  have hiso := S.iform_rhoTwist v
  have hinj := injective_of_iform _ hiso
  have hfin : Ψ.Finite := famTwoDHigh_finite_of_isRootComponent hΨ
  have hf : IsIsometry Ψ (S.rhoTwist v) :=
    ⟨(hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj.injOn, fun γ _ δ' _ => hiso γ δ',
      fun γ _ => map_neg _ γ⟩
  have hΔ : ∀ β ∈ simpleRoots Ψ, S.rhoTwist v β ∈ simpleRoots Ψ :=
    fun β hβ => hf.apply_mem_simpleRoots hΨ hpos hβ
  obtain ⟨Q, hQT, hQG, hstep⟩ := S.exists_step_frobTwist_adjoint hq
  have hyC : y ∈ adjointGroup τ L := hSC _ hyZ
  have hFc : ∀ g, frobTwistGL τ L r e (y * Q) g = y * S.D.step g * y⁻¹ := by
    intro g
    rw [hstep, frobTwistGL_apply, frobTwistGL_apply]
    group
  have hcT : y * Q ∈ Subgroup.normalizer (torusGroup τ L : Set (ModGL τ L)) :=
    mul_mem (mem_normalizer_torusGroup_of_mem_monomialSubgroup hyM) hQT
  have hcG : (adjointGroup τ L).map (MulAut.conj (y * Q)).toMonoidHom = adjointGroup τ L := by
    have e1 : (MulAut.conj (y * Q)).toMonoidHom =
        (MulAut.conj y).toMonoidHom.comp (MulAut.conj Q).toMonoidHom := by
      ext g
      simp [mul_assoc]
    rw [e1, ← Subgroup.map_map, hQG]
    exact CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hyC)
  have hπ : weylQuotientHom τ L ⟨y, hyM⟩ = v := weylQuotientHom_eq hyv
  have hU : ∀ γ ∈ componentRoots χ i,
      (rootSubgroup τ L γ).map (frobTwistGL τ L r e (y * Q)) =
        rootSubgroup τ L (S.rhoTwist v γ) := by
    intro γ hγ
    have hγr := hΨ.isRoot γ hγ
    have e1 : frobTwistGL τ L r e (y * Q) = (MulAut.conj y).toMonoidHom.comp S.D.step := by
      ext g : 1
      rw [hFc]
      rfl
    rw [e1, ← Subgroup.map_map, S.frob.map_rootSubgroup γ hγr,
      CFSG.RankThree.Lattice.GenFixedRootDatum.map_conj_rootSubgroup_of_mem_monomialSubgroup hyM
        ((S.frob.isRoot_iff γ).2 hγr), hπ]
    rfl
  have hpin' : ∀ β ∈ simpleRoots (componentRoots χ i), ∀ A : SL2 L,
      frobTwistGL τ L r e (y * Q) (rootSL2 τ L β A) =
        rootSL2 τ L (S.rhoTwist v β) (Matrix.SpecialLinearGroup.map (iterateFrobenius L r e) A) :=
    fun β hβ A => by rw [hFc]; exact hpin β hβ A
  obtain ⟨C, hCqs, hCperf, hCle, hcomm⟩ := exists_twoD_core (M := M) (χ := χ) hτ he i
    (S.rhoTwist v) hiso hmaps hpos hG hcT hcG hU hpin'
  have hyZ' : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ) :=
    (sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _) hyZ
  obtain ⟨z, hzZ, hz⟩ := exists_lang_torus_sup_kernelRoots S (s := 1) Nat.one_pos
    (fun γ hγ => by rw [Function.iterate_one]; exact hρ γ hγ) hyZ'
  have hz' : S.D.step z = z * y := by
    rw [iterHom_eq_iterate, Function.iterate_one] at hz
    exact hz
  have hzC : z ∈ adjointGroup τ L := hSC _ hzZ
  have hzN := famTwoDHigh_mem_normalizer_rootSpan_of_mem_Z (χ := χ) hzZ i
  set φ : ModGL τ L →* ModGL τ L := (MulAut.conj z⁻¹).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj z⁻¹).injective
  have hφapp : ∀ g, φ g = z⁻¹ * g * z := fun g => by rw [hφ]; simp
  set M' : Subgroup (ModGL τ L) :=
    adjointGroup τ L ⊓ (frobTwistGL τ L r e (y * Q)).eqLocus (MonoidHom.id _) with hM'
  have hstepz : ∀ g, frobTwistGL τ L r e (y * Q) (z⁻¹ * g * z) = z⁻¹ * S.D.step g * z := by
    intro g
    rw [hFc, map_mul, map_mul, map_inv, hz']
    group
  have hMap : S.D.model.map φ = M' := by
    ext g
    constructor
    · rintro ⟨x, ⟨hxC, hxF⟩, rfl⟩
      have hxs : S.D.step x = x := hxF
      rw [hφapp]
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hzC) hxC) hzC, ?_⟩
      change frobTwistGL τ L r e (y * Q) (z⁻¹ * x * z) = z⁻¹ * x * z
      rw [hstepz, hxs]
    · rintro ⟨hgC, hgF⟩
      have hgF' : frobTwistGL τ L r e (y * Q) g = g := hgF
      refine ⟨z * g * z⁻¹, Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hzC hgC) (inv_mem hzC), ?_⟩, ?_⟩
      · change S.D.step (z * g * z⁻¹) = z * g * z⁻¹
        have h1 := hstepz (z * g * z⁻¹)
        have e2 : z⁻¹ * (z * g * z⁻¹) * z = g := by group
        rw [e2, hgF'] at h1
        calc S.D.step (z * g * z⁻¹) = z * (z⁻¹ * S.D.step (z * g * z⁻¹) * z) * z⁻¹ := by group
          _ = z * g * z⁻¹ := by rw [← h1]
      · rw [hφapp]
        group
  have hRR : rationalRootsM S.ρ χ i = Ψ := by
    rw [hΨdef]
    exact famTwoDHigh_rationalRootsM_eq_of_image_eq i hst
  have hspan : (rootSpan τ L Ψ).map φ = rootSpan τ L Ψ :=
    CFSG.LieType.Chevalley.map_conj_eq_of_mem_normalizer (inv_mem hzN)
  have hRmap : (rationalComponentM S.ρ S.Γ χ i).map φ =
      ⁅rootSpan τ L Ψ ⊓ ⁅M', M'⁆, rootSpan τ L Ψ ⊓ ⁅M', M'⁆⁆ := by
    rw [rationalComponentM, rationalSpanM, hRR, Subgroup.map_commutator,
      Subgroup.map_inf_eq _ _ _ hφinj, hspan]
    change ⁅_ ⊓ (⁅S.D.model, S.D.model⁆).map φ, _ ⊓ (⁅S.D.model, S.D.model⁆).map φ⁆ = _
    rw [Subgroup.map_commutator, hMap]
  have hRC : (rationalComponentM S.ρ S.Γ χ i).map φ = C := by
    rw [hRmap]
    have hCC : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.1 hCperf
    have hle : rootSpan τ L Ψ ⊓ ⁅M', M'⁆ ≤ rootSpan τ L Ψ ⊓ M' :=
      inf_le_inf_left _ (Subgroup.commutator_le_self M')
    refine le_antisymm (le_trans (Subgroup.commutator_mono hle hle) hcomm) ?_
    have hCM : C ≤ M' := hCle.trans inf_le_right
    have hCle' : C ≤ rootSpan τ L Ψ ⊓ ⁅M', M'⁆ := by
      refine le_inf (hCle.trans inf_le_left) ?_
      rw [← hCC]
      exact Subgroup.commutator_mono hCM hCM
    calc C = ⁅C, C⁆ := hCC.symm
      _ ≤ _ := Subgroup.commutator_mono hCle' hCle'
  have e' : rationalComponentM S.ρ S.Γ χ i ≃* C :=
    ((rationalComponentM S.ρ S.Γ χ i).equivMapOfInjective φ hφinj).trans
      (MulEquiv.subgroupCongr hRC)
  exact isQuasisimple_of_mulEquiv' e'.symm hCqs

end CFSG.StandardType.TableCRes

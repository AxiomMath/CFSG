module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6RootLangTransitive
public import CFSG.LocalAnalysis.StandardType.ExcPos.LangFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCTw
public import CFSG.LocalAnalysis.StandardType.GGFinModelIndex
public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6Scalar
public import CFSG.LieType.Chevalley.RootCharacterConjugation

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.StandardType.GGFinModel CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Exceptional
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem map_ggPhi_rootSubgroup_twistedE6 (f : ℕ)
    {α : Fin (langTag .twistedE6).rank → ℤ} (hα : IsRoot (langTag .twistedE6) α) :
    (rootSubgroup (langTag .twistedE6) GGL α).map (ggPhi .twistedE6 f) =
      rootSubgroup (langTag .twistedE6) GGL (rho α) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hz
    rw [ggPhi_pinnedX_twistedE6 f hα]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  · intro hy
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (by positivity : 0 < (2 : ℕ) ^ f)
    refine Subgroup.mem_map.2 ⟨pinnedX (langTag .twistedE6) GGL α d,
      mem_rootSubgroup.2 ⟨d, rfl⟩, ?_⟩
    rw [ggPhi_pinnedX_twistedE6 f hα, hd]
    rfl

theorem ggBC_twistedE6_of_fixed_root (n f : ℕ) (hf : 1 ≤ f)
    {α : Fin (langTag .twistedE6).rank → ℤ} (hα : IsRoot (langTag .twistedE6) α)
    (hρ : rho α = α) :
    ((ggU .twistedE6 n f).D.rootGroup (proj α)).map (ggIotaK .twistedE6 n f hf) =
      rootSubgroup (langTag .twistedE6) GGL α ⊓ ggFixGp .twistedE6 f := by
  have hβ : proj α ∈ (ggU .twistedE6 n f).D.roots :=
    isRoot_iff_mem_roots.1 (isRoot_proj hα)
  rw [ggBC_twistedE6 n f hf (proj α) hβ]
  unfold twistedRootSubgroup
  dsimp +instances only [langTag] at *
  have hsup : (⨆ γ ∈ {a : Fin Tag.E6.rank → ℤ |
        IsRoot Tag.E6 a},
      ⨆ (_ : ∃ c : ℕ, 0 < c ∧ orbitSum orbitMap γ = c • proj α),
        rootSubgroup Tag.E6 GGL γ) =
      rootSubgroup Tag.E6 GGL α := by
    apply le_antisymm
    · refine iSup_le fun γ => iSup_le fun hγ => iSup_le fun hc => ?_
      obtain ⟨c, hcpos, hc⟩ := hc
      change proj γ = c • proj α at hc
      have hc1 := eq_one_of_proj_eq_nsmul hγ hα hcpos hc
      simp only [hc1, one_nsmul] at hc
      have hγα : γ = α := by
        rcases (proj_eq_proj_iff hα hγ).1 hc.symm with h | h
        · exact h
        · exact h.trans hρ
      subst γ
      exact le_rfl
    · exact le_iSup_of_le α (le_iSup_of_le hα
        (le_iSup_of_le ⟨1, Nat.zero_lt_one, by simpa only [one_nsmul] using (proj_apply α).symm⟩
          le_rfl))
  erw [hsup, ggFixGp]
  dsimp +instances only [langTag]
  erw [← inf_assoc, inf_eq_left.2 (rootSubgroup_le_adjointGroup α)]
  rfl

theorem exists_native_factor_of_twisted_fixed (n f : ℕ) (hf : 1 ≤ f)
    {y : ModGL (langTag .twistedE6) GGL}
    (hy : y ∈ adjointGroup (langTag .twistedE6) GGL)
    (hfix : ggPhi .twistedE6 f y = y) :
    ∃ k : (ggU .twistedE6 n f).K, ∃ t ∈ torusGroup (langTag .twistedE6) GGL,
      y = ggIotaK .twistedE6 n f hf k * t := by
  let K := GaloisField 2 (2 * f)
  letI : Algebra K GGL := (ggRatEmb (2 * f)).toAlgebra
  haveI : IsScalarTower (ZMod 2) K GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : Algebra.IsAlgebraic K GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) (A := GGL)
  haveI : IsAlgClosure K GGL := ⟨IsAlgClosure.isAlgClosed (ZMod 2), inferInstance⟩
  have hmul := (CFSG.RankThree.Classical2.twisted_E6_full_rational_fixed_group_order
    Nat.prime_two hf K (card_galoisField_two_mul 2 f hf) (frobQ 2 f)
    (frobQ_apply 2 f) GGL (ggFrobT f) (ggFrobT_apply f)).2.1
  have hyR : y⁻¹ ∈ twistedFixedGroup TwistTag.E6 GGL (ggFrobT f) := by
    apply Subgroup.inv_mem
    exact (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 GGL (ggFrobT f)).2 ⟨hy, hfix⟩
  change y⁻¹ ∈ (twistedFixedGroup TwistTag.E6 GGL (ggFrobT f) :
    Set (ModGL TwistTag.E6.tag GGL)) at hyR
  rw [hmul] at hyR
  obtain ⟨t, ht, u', hu', htu⟩ := hyR
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hu'
  let b : GGKb .twistedE6 n f := (ggKbEquivTwE6 n f hf).symm ⟨u, hu⟩
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (ggU .twistedE6 n f).K) b
  have hku : ggIotaK .twistedE6 n f hf k = baseChangeGL (ggRatEmb (2 * f)) u := by
    rw [ggIotaK, MonoidHom.comp_apply, hk]
    change baseChangeGL (ggRatEmb (2 * f))
      ((ggKbEquivTwE6 n f hf b : graphFixedRootGroup TwistTag.E6 K (frobQ 2 f)) :
        ModGL TwistTag.E6.tag K) = _
    simp only [b, MulEquiv.apply_symm_apply]
  refine ⟨k⁻¹, t⁻¹, Subgroup.inv_mem _ ht.1, ?_⟩
  have heq : t * baseChangeGL (ggRatEmb (2 * f)) u = y⁻¹ := htu
  dsimp +instances only [langTag, TwistTag.tag] at *
  erw [map_inv, hku, ← mul_inv_rev, heq, inv_inv]

namespace ExcLangFrame

theorem exists_rootSub_twistedE6 {X : Type} [Group X] {n f p : ℕ}
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ B₁ D : Subgroup X} {x : X}
    (hψ : ψ.range = G₀) (F : ExcLangFrame .twistedE6 n f p ψ G₀ B₁ D x)
    {α : Fin (langTag .twistedE6).rank → ℤ}
    {w : ModGL (langTag .twistedE6) GGL} (hα : IsRoot (langTag .twistedE6) α)
    (hw : w ∈ adjointGroup (langTag .twistedE6) GGL)
    (hV : (excCurve α w).map F.Δ.step = excCurve α w)
    (hVm : (excCurve (-α) w).map F.Δ.step = excCurve (-α) w) :
    ∃ (β : Fin (ggU .twistedE6 n f).D.rank → ℤ) (k : (ggU .twistedE6 n f).K),
      β ∈ (ggU .twistedE6 n f).D.roots ∧ GGLongRoot (ggU .twistedE6 n f).D β ∧
      ((ggRootSub (ggU .twistedE6 n f).D ψ β k).subgroupOf G₀).map F.η =
        excCurve α w ⊓ F.Δ.model ∧
      ((ggRootSub (ggU .twistedE6 n f).D ψ (-β) k).subgroupOf G₀).map F.η =
        excCurve (-α) w ⊓ F.Δ.model := by
  let g0 := F.Δ.g0
  let A := adjointGroup (langTag .twistedE6) GGL
  let M := F.Δ.model
  let Gg := ggFixGp .twistedE6 f
  let ι := ggIotaK .twistedE6 n f F.one_le_f
  let α0 : Fin (langTag .twistedE6).rank → ℤ := Pi.single 1 1
  let β : Fin (ggU .twistedE6 n f).D.rank → ℤ := proj α0
  let V0 := excCurve α0 g0⁻¹
  let Vm0 := excCurve (-α0) g0⁻¹
  let ψ₀ : (ggU .twistedE6 n f).K →* ↥G₀ :=
    ψ.codRestrict G₀ (fun k => hψ ▸ MonoidHom.mem_range.2 ⟨k, rfl⟩)
  let ηψ := F.η.comp ψ₀
  have hα0 : IsRoot (langTag .twistedE6) α0 := isRoot_single .E6 1
  have hα0m : IsRoot (langTag .twistedE6) (-α0) := isRoot_neg_single .E6 1
  have hρ0 : rho α0 = α0 := by
    change rho (Pi.single (1 : Fin 6) 1) = Pi.single (1 : Fin 6) 1
    funext j
    fin_cases j <;> rfl
  have hρ0m : rho (-α0) = -α0 := by
    change -rho α0 = -α0
    rw [hρ0]
    rfl
  have hβ : β ∈ (ggU .twistedE6 n f).D.roots :=
    isRoot_iff_mem_roots.1 (isRoot_proj hα0)
  have hβlong : GGLongRoot (ggU .twistedE6 n f).D β := by
    change GGLongRoot (ggU .twistedE6 0 f).D (proj (Pi.single (1 : Fin 6) 1))
    exact CFSG.ClassicalInvolution.Phan.PhanE.twistedE6_fixed_simple_long 1 rfl
  have hηψ : ηψ = (MulAut.conj g0⁻¹).toMonoidHom.comp ι := by
    refine MonoidHom.ext fun k => ?_
    change F.η (ψ₀ k) = g0⁻¹ * ι k * g0
    rw [F.η_eq]
    change g0⁻¹ * F.θ (ψ₀ k) * g0 = g0⁻¹ * ι k * g0
    have hθ : F.θ (ψ₀ k) = ι k :=
      F.θ_iota k (hψ ▸ MonoidHom.mem_range.2 ⟨k, rfl⟩)
    rw [hθ]
  have hsymm : (MulAut.conj g0).symm.toMonoidHom =
      (MulAut.conj g0⁻¹).toMonoidHom := by
    refine MonoidHom.ext fun z => ?_
    simp [MulAut.conj]
  have hM : Gg.map (MulAut.conj g0⁻¹).toMonoidHom = M := by
    rw [← hsymm]
    apply (Subgroup.map_symm_eq_iff_map_eq M (e := MulAut.conj g0)).2
    change F.Δ.model.map (MulAut.conj F.Δ.g0).toMonoidHom = ggFixGp .twistedE6 f
    exact F.Δ.map_conj_model.trans (ggFixGp_eq_fix F.Δ F.Φ_eq)
  have hstepmap : F.Δ.step.comp (MulAut.conj g0⁻¹).toMonoidHom =
      (MulAut.conj g0⁻¹).toMonoidHom.comp (ggPhi .twistedE6 f) := by
    simpa only [F.Φ_eq] using F.Δ.step_comp_conj_g0_inv
  have hstable : ∀ δ : Fin (langTag .twistedE6).rank → ℤ,
      IsRoot (langTag .twistedE6) δ → rho δ = δ →
        (excCurve δ g0⁻¹).map F.Δ.step = excCurve δ g0⁻¹ := by
    intro δ hδ hρ
    change ((rootSubgroup (langTag .twistedE6) GGL δ).map
      (MulAut.conj g0⁻¹).toMonoidHom).map F.Δ.step = _
    rw [Subgroup.map_map, hstepmap, ← Subgroup.map_map,
      map_ggPhi_rootSubgroup_twistedE6 f hδ, hρ]
    rfl
  obtain ⟨h', hh', hH', hHm'⟩ := exists_conj_stableOppositePair F.one_le_f F.Δ F.q_eq
    hα0 hα (A.inv_mem F.Δ.g0_mem) hw (hstable α0 hα0 hρ0)
    (hstable (-α0) hα0m hρ0m) hV hVm
  let h : ModGL (langTag .twistedE6) GGL := h'
  have hh : h ∈ M := hh'
  have hH : V0.map (MulAut.conj h).toMonoidHom = excCurve α w := hH'
  have hHm : Vm0.map (MulAut.conj h).toMonoidHom = excCurve (-α) w := hHm'
  have hyA : g0 * h * g0⁻¹ ∈ A :=
    A.mul_mem (A.mul_mem F.Δ.g0_mem (F.Δ.mem_model.1 hh).1) (A.inv_mem F.Δ.g0_mem)
  have hyfix : ggPhi .twistedE6 f (g0 * h * g0⁻¹) = g0 * h * g0⁻¹ := by
    apply (MulAut.conj g0⁻¹).injective
    simp only [MulAut.conj_apply, inv_inv]
    have hstep := congrArg (fun φ : ModGL (langTag .twistedE6) GGL →*
      ModGL (langTag .twistedE6) GGL => φ (g0 * h * g0⁻¹)) F.Δ.step_comp_conj_g0_inv
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv, F.Φ_eq] at hstep
    rw [← hstep]
    have he : g0⁻¹ * (g0 * h * g0⁻¹) * g0 = h := by group
    rw [he]
    exact (F.Δ.mem_model.1 hh).2
  obtain ⟨k, t, ht, hkt⟩ := exists_native_factor_of_twisted_fixed n f F.one_le_f hyA hyfix
  let c := ηψ k
  let s := g0⁻¹ * t * g0
  have hc : c = g0⁻¹ * ι k * g0 := by
    change ηψ k = _
    rw [hηψ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hprod : h = c * s := by
    rw [hc]
    apply (MulAut.conj g0).injective
    simp only [MulAut.conj_apply]
    change g0 * h * g0⁻¹ = g0 * ((g0⁻¹ * ι k * g0) * (g0⁻¹ * t * g0)) * g0⁻¹
    rw [hkt]
    group
    rfl
  obtain ⟨a, hta⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have htroot : ∀ δ, IsRoot (langTag .twistedE6) δ →
      (rootSubgroup (langTag .twistedE6) GGL δ).map (MulAut.conj t).toMonoidHom =
        rootSubgroup (langTag .twistedE6) GGL δ := by
    intro δ hδ
    rw [hta]
    exact map_conj_rootDiagUnit_rootSubgroup a hδ
  have hscomp : (MulAut.conj s).toMonoidHom.comp (MulAut.conj g0⁻¹).toMonoidHom =
      (MulAut.conj g0⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom := by
    refine MonoidHom.ext fun z => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    dsimp only [s]
    group
  have hsroot : ∀ δ, IsRoot (langTag .twistedE6) δ →
      (excCurve δ g0⁻¹).map (MulAut.conj s).toMonoidHom = excCurve δ g0⁻¹ := by
    intro δ hδ
    change ((rootSubgroup (langTag .twistedE6) GGL δ).map
      (MulAut.conj g0⁻¹).toMonoidHom).map (MulAut.conj s).toMonoidHom = _
    rw [Subgroup.map_map, hscomp, ← Subgroup.map_map, htroot δ hδ]
    rfl
  have hconjprod : (MulAut.conj h).toMonoidHom =
      (MulAut.conj c).toMonoidHom.comp (MulAut.conj s).toMonoidHom := by
    rw [hprod]
    refine MonoidHom.ext fun z => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcV : V0.map (MulAut.conj c).toMonoidHom = excCurve α w := by
    rw [hconjprod, ← Subgroup.map_map, hsroot α0 hα0] at hH
    exact hH
  have hcVm : Vm0.map (MulAut.conj c).toMonoidHom = excCurve (-α) w := by
    rw [hconjprod, ← Subgroup.map_map, hsroot (-α0) hα0m] at hHm
    exact hHm
  have hcM : c ∈ M := by
    have hcr : c ∈ F.η.range := ⟨ψ₀ k, rfl⟩
    rw [F.range_η] at hcr
    change c ∈ ⁅M, M⁆ at hcr
    have hle := Subgroup.commutator_le_sup (H₁ := M) (H₂ := M)
    rw [sup_idem] at hle
    exact hle hcr
  have hMc : M.map (MulAut.conj c).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (M.le_normalizer hcM)
  have hroot : ∀ δ : Fin (langTag .twistedE6).rank → ℤ,
      IsRoot (langTag .twistedE6) δ → rho δ = δ →
        ((ggU .twistedE6 n f).D.rootGroup (proj δ)).map ηψ = excCurve δ g0⁻¹ ⊓ M := by
    intro δ hδ hρ
    rw [hηψ, ← Subgroup.map_map, ggBC_twistedE6_of_fixed_root n f F.one_le_f hδ hρ]
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g0⁻¹).injective, hM]
    rfl
  have hrootp : ((ggU .twistedE6 n f).D.rootGroup β).map ηψ = V0 ⊓ M :=
    hroot α0 hα0 hρ0
  have hrootm : ((ggU .twistedE6 n f).D.rootGroup (-β)).map ηψ = Vm0 ⊓ M := by
    have hp : proj (-α0) = -β := by
      change proj (-α0) = -proj α0
      exact map_neg proj α0
    have hr := hroot (-α0) hα0m hρ0m
    erw [hp] at hr
    exact hr
  have hconj : (MulAut.conj c).toMonoidHom.comp ηψ =
      ηψ.comp (MulAut.conj k).toMonoidHom := by
    refine MonoidHom.ext fun u => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv]
    rfl
  refine ⟨β, k, hβ, hβlong, ?_, ?_⟩
  · rw [F.map_rootSub_eq_map_codRestrict hψ β k]
    change (((ggU .twistedE6 n f).D.rootGroup β).map
      (MulAut.conj k).toMonoidHom).map ηψ = _
    rw [Subgroup.map_map, ← hconj, ← Subgroup.map_map, hrootp,
      Subgroup.map_inf _ _ _ (MulAut.conj c).injective, hcV, hMc]
  · rw [F.map_rootSub_eq_map_codRestrict hψ (-β) k]
    change (((ggU .twistedE6 n f).D.rootGroup (-β)).map
      (MulAut.conj k).toMonoidHom).map ηψ = _
    rw [Subgroup.map_map, ← hconj, ← Subgroup.map_map, hrootm,
      Subgroup.map_inf _ _ _ (MulAut.conj c).injective, hcVm, hMc]

end ExcLangFrame

end CFSG.StandardType.LieKnownR2.ExcPos

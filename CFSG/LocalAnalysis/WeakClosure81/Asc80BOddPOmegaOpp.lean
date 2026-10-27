module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataBasic
public import CFSG.LieType.SeitzGeneration.OrthHyperRad

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open Subgroup Matrix QuadraticMap
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.LieType.SeitzGeneration

variable {K : Type} [Field K] [Finite K] {d : ℕ}
  {Q : QuadraticForm K (Fin d → K)}

omit [Finite K] in
private theorem polar_coordinateSemilinearMap {g : similarityPairs Q} (u v : Fin d → K) :
    polar Q (coordinateSemilinearMap g.val u) (coordinateSemilinearMap g.val v) =
      (multiplier Q g : K) * g.val.right (polar Q u v) := by
  have hu := multiplier_spec Q g u
  have hv := multiplier_spec Q g v
  have h := multiplier_spec Q g (u + v)
  rw [map_add] at h
  rw [QuadraticMap.map_add Q (coordinateSemilinearMap g.val u)
    (coordinateSemilinearMap g.val v)] at h
  rw [QuadraticMap.map_add Q u v] at h
  rw [map_add] at h
  rw [map_add] at h
  rw [hu, hv, mul_add, mul_add] at h
  linear_combination h

omit [Finite K] in
private theorem coordinateSemilinearMap_inv_smul (g : coordinateSemilinearGroup d K) (a : K)
    (v : Fin d → K) :
    (coordinateSemilinearMap g).symm (a • v) =
      g.right.symm a • (coordinateSemilinearMap g).symm v := by
  have h := coordinateSemilinearMap_smul (g := g⁻¹) a v
  rwa [coordinateSemilinearGroup_inv_field, coordinateSemilinearMap_inv] at h

omit [Finite K] in
private theorem coordinateSemilinearMap_mem_qPerp {G : Subgroup (coordinateSemilinearGroup d K)}
    (hGQ : G ≤ similarityPairs Q) {W : Submodule K (Fin d → K)}
    (hst : ∀ g ∈ G, ∀ w ∈ W, coordinateSemilinearMap g w ∈ W)
    {g : coordinateSemilinearGroup d K} (hg : g ∈ G) {v : Fin d → K}
    (hv : v ∈ qPerp Q W) : coordinateSemilinearMap g v ∈ qPerp Q W := by
  intro w hw
  have hleft : coordinateSemilinearMap g (coordinateSemilinearMap g⁻¹ w) = w := by
    rw [← coordinateSemilinearMap_mul, mul_inv_cancel, coordinateSemilinearMap_one]
  have hw' : coordinateSemilinearMap g⁻¹ w ∈ W := hst g⁻¹ (G.inv_mem hg) w hw
  let gs : similarityPairs Q := ⟨g, hGQ hg⟩
  calc polar Q w (coordinateSemilinearMap g v)
      = polar Q (coordinateSemilinearMap g (coordinateSemilinearMap g⁻¹ w))
          (coordinateSemilinearMap g v) := by rw [hleft]
    _ = (multiplier Q gs : K) *
          g.right (polar Q (coordinateSemilinearMap g⁻¹ w) v) :=
        polar_coordinateSemilinearMap (g := gs) _ _
    _ = 0 := by rw [hv _ hw', map_zero, mul_zero]

theorem exists_stable_opposite {K : Type} [Field K] [Finite K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (h2 : (2 : K) ≠ 0) (hnd : Q.polarBilin.Nondegenerate)
    (G : Subgroup (coordinateSemilinearGroup d K)) (hGQ : G ≤ similarityPairs Q)
    (hG : (Nat.card G : K) ≠ 0) {W : Submodule K (Fin d → K)} (hW : ∀ x ∈ W, Q x = 0)
    (hst : ∀ g ∈ G, ∀ w ∈ W, coordinateSemilinearMap g w ∈ W) :
    ∃ Y : Submodule K (Fin d → K), (∀ y ∈ Y, Q y = 0) ∧ IsCompl Y (qPerp Q W) ∧
      ∀ g ∈ G, ∀ y ∈ Y, coordinateSemilinearMap g y ∈ Y :=
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  letI : Finite (coordinateSemilinearGroup d K) :=
    Finite.of_injective (fun g : coordinateSemilinearGroup d K => (g.left, g.right))
      (fun _ _ h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  letI : Fintype G := Fintype.ofFinite G
  by
  classical
  let Wperp : Submodule K (Fin d → K) := qPerp Q W
  have hWperp : W ≤ Wperp := le_qPerp_of_singular hW
  have hqPerp_eq : Wperp = LinearMap.BilinForm.orthogonal Q.polarBilin W := by
    ext v
    simp only [Wperp]
    rw [mem_qPerp, LinearMap.BilinForm.mem_orthogonal_iff]
    simp only [polarBilin_apply_apply]
  obtain ⟨Y₁, hY₁⟩ := Submodule.exists_isCompl Wperp
  let P₁ : (Fin d → K) →ₗ[K] (Fin d → K) :=
    Wperp.subtype ∘ₗ Submodule.linearProjOfIsCompl Wperp Y₁ hY₁
  have hP₁_mem : ∀ v, P₁ v ∈ Wperp := fun v => (Submodule.linearProjOfIsCompl Wperp Y₁ hY₁ v).2
  have hP₁_fix : ∀ u ∈ Wperp, P₁ u = u := by
    intro u hu
    have := Submodule.linearProjOfIsCompl_apply_left hY₁ ⟨u, hu⟩
    exact congrArg Subtype.val this
  let σ (g : G) : (Fin d → K) ≃+ (Fin d → K) :=
    coordinateSemilinearMap (g : coordinateSemilinearGroup d K)
  let Pg (g : G) : (Fin d → K) →ₗ[K] (Fin d → K) :=
    { toFun := fun v => σ g (P₁ ((σ g).symm v))
      map_add' := by
        intro v w
        simp only [map_add]
      map_smul' := by
        intro a v
        show σ g (P₁ ((σ g).symm (a • v))) = a • σ g (P₁ ((σ g).symm v))
        rw [coordinateSemilinearMap_inv_smul]
        rw [map_smul, coordinateSemilinearMap_smul, RingEquiv.apply_symm_apply] }
  have hPg_mem : ∀ g : G, ∀ v, Pg g v ∈ Wperp := by
    intro g v
    exact coordinateSemilinearMap_mem_qPerp hGQ hst g.2 (hP₁_mem _)
  have hPg_fix : ∀ g : G, ∀ u ∈ Wperp, Pg g u = u := by
    intro g u hu
    have hu' : (σ g).symm u ∈ Wperp := by
      have := coordinateSemilinearMap_mem_qPerp (G := G) hGQ hst
        (g := ((g⁻¹ : G) : coordinateSemilinearGroup d K)) (g⁻¹).2 hu
      simpa [σ, coordinateSemilinearMap_inv] using this
    show σ g (P₁ ((σ g).symm u)) = u
    rw [hP₁_fix _ hu']
    exact AddEquiv.apply_symm_apply (σ g) u
  let c : K := ((Fintype.card G : ℕ) : K)
  have hc : c ≠ 0 := by
    have h := hG
    rw [Nat.card_eq_fintype_card] at h
    simpa [c] using h
  let Pstar : (Fin d → K) →ₗ[K] (Fin d → K) :=
    c⁻¹ • ∑ g : G, Pg g
  have hPstar_mem : ∀ v, Pstar v ∈ Wperp := by
    intro v
    simp only [Pstar]
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
    exact Wperp.smul_mem _ (by
      apply Submodule.sum_mem
      intro g _
      exact hPg_mem g v)
  have hPstar_fix : ∀ u ∈ Wperp, Pstar u = u := by
    intro u hu
    have hsum : ∑ g : G, Pg g u = Fintype.card G • u := by
      rw [Finset.sum_congr rfl (fun g _ => hPg_fix g u hu), Finset.sum_const, Finset.card_univ]
    simp only [Pstar]
    rw [LinearMap.smul_apply, LinearMap.sum_apply, hsum, ← Nat.cast_smul_eq_nsmul K,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hPstar_comm : ∀ (h : G) (v : Fin d → K), σ h (Pstar v) = Pstar (σ h v) := by
    intro h v
    have hcφ : ((h : G) : coordinateSemilinearGroup d K).right c⁻¹ = c⁻¹ := by
      rw [map_inv₀, map_natCast]
    have hstep : ∀ g : G, σ h (Pg g v) = Pg (h * g) (σ h v) := by
      intro g
      have hcoe : ((h * g : G) : coordinateSemilinearGroup d K) =
          (h : coordinateSemilinearGroup d K) * (g : coordinateSemilinearGroup d K) := rfl
      change coordinateSemilinearMap ((h : G) : coordinateSemilinearGroup d K)
          (coordinateSemilinearMap ((g : G) : coordinateSemilinearGroup d K)
            (P₁ ((coordinateSemilinearMap ((g : G) : coordinateSemilinearGroup d K)).symm v))) =
        coordinateSemilinearMap ((h * g : G) : coordinateSemilinearGroup d K)
          (P₁ ((coordinateSemilinearMap ((h * g : G) : coordinateSemilinearGroup d K)).symm
            (coordinateSemilinearMap ((h : G) : coordinateSemilinearGroup d K) v)))
      rw [hcoe]
      rw [← coordinateSemilinearMap_mul]
      congr 1
      have harg : (coordinateSemilinearMap ((h : coordinateSemilinearGroup d K) *
            (g : coordinateSemilinearGroup d K))).symm
          (coordinateSemilinearMap ((h : G) : coordinateSemilinearGroup d K) v) =
          (coordinateSemilinearMap ((g : G) : coordinateSemilinearGroup d K)).symm v := by
        apply (coordinateSemilinearMap ((h : coordinateSemilinearGroup d K) *
          (g : coordinateSemilinearGroup d K))).injective
        rw [AddEquiv.apply_symm_apply, coordinateSemilinearMap_mul, AddEquiv.apply_symm_apply]
      rw [harg]
    simp only [Pstar]
    conv_rhs => rw [LinearMap.smul_apply, LinearMap.sum_apply]
    rw [LinearMap.smul_apply, LinearMap.sum_apply, coordinateSemilinearMap_smul, hcφ, map_sum,
      Finset.sum_congr rfl (fun g _ => hstep g),
      Fintype.sum_equiv (Equiv.mulLeft h)
        (fun g : G => Pg (h * g) (σ h v)) (fun g : G => Pg g (σ h v)) (fun g => rfl)]
  let f : (Fin d → K) →ₗ[K] Wperp := Pstar.codRestrict Wperp hPstar_mem
  have hf : ∀ x : Wperp, f x = x := fun x => Subtype.ext (hPstar_fix x x.2)
  have hcomplW : IsCompl Wperp (LinearMap.ker f) := LinearMap.isCompl_of_proj hf
  let Y₀ : Submodule K (Fin d → K) := LinearMap.ker f
  have hY0_stab : ∀ (g : G) (y : Y₀), σ g y ∈ Y₀ := by
    intro g y
    have hy' : Pstar y = 0 := by
      have := congrArg Subtype.val (LinearMap.mem_ker.mp y.2)
      rwa [LinearMap.codRestrict_apply] at this
    refine LinearMap.mem_ker.mpr (Subtype.ext ?_)
    rw [LinearMap.codRestrict_apply]
    rw [← hPstar_comm g y, hy', map_zero]
    rfl
  let p : W →ₗ[K] Module.Dual K Y₀ :=
    { toFun := fun w => (Q.polarBilin (w : Fin d → K)).comp Y₀.subtype
      map_add' := by
        intro w₁ w₂
        ext y
        rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.coe_add,
          map_add, LinearMap.add_apply, LinearMap.comp_apply]
      map_smul' := by
        intro a w
        ext y
        rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.coe_smul,
          map_smul, LinearMap.smul_apply]
        rfl }
  have hp_inj : Function.Injective p := by
    intro w₁ w₂ h
    have hsub : p (w₁ - w₂) = 0 := by rw [map_sub, h, sub_self]
    have hpair : ∀ v : Fin d → K, polar Q ((w₁ - w₂ : W) : Fin d → K) v = 0 := by
      intro v
      have hv : v ∈ Y₀ ⊔ Wperp := by rw [hcomplW.symm.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
      have h1 : polar Q ((w₁ - w₂ : W) : Fin d → K) (y : Fin d → K) = 0 := by
        have := congrArg (fun φ : Module.Dual K Y₀ => φ ⟨y, hy⟩) hsub
        simpa [p, LinearMap.comp_apply, polarBilin_apply_apply] using this
      have h2 : polar Q ((w₁ - w₂ : W) : Fin d → K) (z : Fin d → K) = 0 :=
        mem_qPerp.mp hz (w₁ - w₂) (w₁ - w₂).2
      rw [polar_add_right, h1, h2, add_zero]
    have hzero : ((w₁ - w₂ : W) : Fin d → K) = 0 :=
      hnd.1 ((w₁ - w₂ : W) : Fin d → K) (fun v => by
        rw [polarBilin_apply_apply]; exact hpair v)
    exact sub_eq_zero.mp (Subtype.ext hzero)
  have hp_flip_inj : Function.Injective p.flip := by
    intro y₁ y₂ h
    have hsub : p.flip (y₁ - y₂) = 0 := by rw [map_sub, h, sub_self]
    have hmem : ((y₁ - y₂ : Y₀) : Fin d → K) ∈ Wperp := by
      rw [hqPerp_eq, LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      have := congrArg (fun φ : Module.Dual K W => φ ⟨w, hw⟩) hsub
      simpa [p, LinearMap.flip_apply, LinearMap.comp_apply, polarBilin_apply_apply] using this
    have hbot : ((y₁ - y₂ : Y₀) : Fin d → K) ∈ (⊥ : Submodule K (Fin d → K)) := by
      have hinf : ((y₁ - y₂ : Y₀) : Fin d → K) ∈ Y₀ ⊓ Wperp := ⟨(y₁ - y₂).2, hmem⟩
      rwa [disjoint_iff.mp hcomplW.symm.disjoint] at hinf
    have hzero : ((y₁ - y₂ : Y₀) : Fin d → K) = 0 := by
      rwa [Submodule.mem_bot] at hbot
    exact sub_eq_zero.mp (Subtype.ext hzero)
  have hp_perf : p.IsPerfPair := LinearMap.IsPerfPair.of_injective hp_inj hp_flip_inj
  let e : W ≃ₗ[K] Module.Dual K Y₀ := by
    haveI : p.IsPerfPair := hp_perf
    exact p.toPerfPair
  let r : Y₀ →ₗ[K] Module.Dual K Y₀ :=
    { toFun := fun y => (Q.polarBilin (y : Fin d → K)).comp Y₀.subtype
      map_add' := by
        intro y₁ y₂
        ext y'
        rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.coe_add,
          map_add, LinearMap.add_apply, LinearMap.comp_apply]
      map_smul' := by
        intro a y
        ext y'
        rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.coe_smul,
          map_smul, LinearMap.smul_apply]
        rfl }
  let θ : Y₀ →ₗ[K] W :=
    e.symm.toLinearMap.comp ((-(2 : K)⁻¹) • r)
  have hθ : ∀ y y' : Y₀, polar Q (θ y : Fin d → K) (y' : Fin d → K) =
      -(2 : K)⁻¹ * polar Q (y : Fin d → K) (y' : Fin d → K) := by
    intro y y'
    have h1 : e (θ y) = -(2 : K)⁻¹ • r y := by
      simp only [θ]
      rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
        LinearMap.smul_apply]
    have h2 := congrArg (fun φ : Module.Dual K Y₀ => φ y') h1
    simp only [e] at h2
    rw [LinearMap.toPerfPair_apply, LinearMap.smul_apply] at h2
    simpa [p, r, LinearMap.comp_apply, smul_eq_mul, polarBilin_apply_apply] using h2
  let φ : Y₀ →ₗ[K] (Fin d → K) := Y₀.subtype + W.subtype.comp θ
  have hφ_apply : ∀ y : Y₀, φ y = (y : Fin d → K) + (θ y : Fin d → K) := fun y => rfl
  let Y : Submodule K (Fin d → K) := Submodule.map φ ⊤
  have hY_sing : ∀ y ∈ Y, Q y = 0 := by
    intro y hy
    simp only [Y, Submodule.mem_map] at hy
    obtain ⟨y₀, -, rfl⟩ := hy
    rw [hφ_apply, QuadraticMap.map_add Q (y₀ : Fin d → K) (θ y₀ : Fin d → K),
      hW (θ y₀ : Fin d → K) (θ y₀).2, add_zero]
    have hθy := hθ y₀ y₀
    rw [polar_comm] at hθy
    rw [hθy, polar_self, two_smul]
    field_simp
    ring
  have hY_compl : IsCompl Y Wperp := by
    have hdisj : Disjoint Y Wperp := by
      rw [disjoint_iff, ← le_bot_iff]
      intro v hv
      rw [Submodule.mem_inf] at hv
      obtain ⟨hvY, hvW⟩ := hv
      simp only [Y, Submodule.mem_map] at hvY
      obtain ⟨y₀, -, rfl⟩ := hvY
      rw [hφ_apply] at hvW ⊢
      have hy0W : (y₀ : Fin d → K) ∈ Wperp := by
        have hθW : (θ y₀ : Fin d → K) ∈ Wperp := hWperp (θ y₀).2
        have hsub : (y₀ : Fin d → K) + (θ y₀ : Fin d → K) - (θ y₀ : Fin d → K) =
            (y₀ : Fin d → K) := by abel
        have := Wperp.sub_mem hvW hθW
        rwa [hsub] at this
      have hbot : (y₀ : Fin d → K) ∈ (⊥ : Submodule K (Fin d → K)) := by
        have hinf : (y₀ : Fin d → K) ∈ Y₀ ⊓ Wperp := ⟨y₀.2, hy0W⟩
        rwa [disjoint_iff.mp hcomplW.symm.disjoint] at hinf
      have hy0 : (y₀ : Fin d → K) = 0 := by rwa [Submodule.mem_bot] at hbot
      have hy0' : y₀ = 0 := Subtype.ext hy0
      rw [Submodule.mem_bot, hy0']
      simp
    have hcodisj : Codisjoint Y Wperp := by
      rw [codisjoint_iff]
      apply top_le_iff.mp
      intro v hv
      have hmem : v ∈ Y₀ ⊔ Wperp := by
        rw [hcomplW.symm.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨y₀, hy₀, z, hz, rfl⟩ := Submodule.mem_sup.mp hmem
      let ysub : Y₀ := ⟨y₀, hy₀⟩
      have hYmem : (y₀ : Fin d → K) + (θ ysub : Fin d → K) ∈ Y := by
        simp only [Y, Submodule.mem_map]
        exact ⟨ysub, Submodule.mem_top, rfl⟩
      have hWmem : (z : Fin d → K) - (θ ysub : Fin d → K) ∈ Wperp :=
        Wperp.sub_mem hz (hWperp (θ ysub).2)
      have hsum : ((y₀ : Fin d → K) + (θ ysub : Fin d → K)) +
          ((z : Fin d → K) - (θ ysub : Fin d → K)) = (y₀ : Fin d → K) + (z : Fin d → K) := by
        abel
      rw [← hsum]
      exact Submodule.add_mem_sup hYmem hWmem
    exact ⟨hdisj, hcodisj⟩
  refine ⟨Y, hY_sing, hY_compl, ?_⟩
  intro g hg y hy
  simp only [Y, Submodule.mem_map] at hy
  obtain ⟨y₀, -, rfl⟩ := hy
  let gs : G := ⟨g, hg⟩
  let gsp : similarityPairs Q := ⟨g, hGQ hg⟩
  have hy0 : σ gs (y₀ : Fin d → K) ∈ Y₀ := hY0_stab gs y₀
  let z : Y₀ := ⟨σ gs (y₀ : Fin d → K), hy0⟩
  have hleft : ∀ v : Fin d → K,
      coordinateSemilinearMap g (coordinateSemilinearMap g⁻¹ v) = v := by
    intro v
    rw [← coordinateSemilinearMap_mul, mul_inv_cancel, coordinateSemilinearMap_one]
  have hθnat : σ gs (θ y₀ : Fin d → K) = (θ z : Fin d → K) := by
    have hw1 : (⟨σ gs (θ y₀ : Fin d → K), hst g hg _ (θ y₀).2⟩ : W) = θ z := by
      apply hp_inj
      ext y'
      have hy'' : σ ⟨g⁻¹, G.inv_mem hg⟩ (y' : Fin d → K) ∈ Y₀ :=
        hY0_stab ⟨g⁻¹, G.inv_mem hg⟩ y'
      let y'' : Y₀ := ⟨σ ⟨g⁻¹, G.inv_mem hg⟩ (y' : Fin d → K), hy''⟩
      have hσy'' : σ gs (y'' : Fin d → K) = (y' : Fin d → K) := by
        change coordinateSemilinearMap g
          (coordinateSemilinearMap g⁻¹ (y' : Fin d → K)) = (y' : Fin d → K)
        exact hleft _
      have hφ2 : g.right (-(2 : K)⁻¹) = -(2 : K)⁻¹ := by
        rw [map_neg, map_inv₀, map_ofNat]
      have hcalc : polar Q (σ gs (θ y₀ : Fin d → K)) (y' : Fin d → K) =
          polar Q (θ z : Fin d → K) (y' : Fin d → K) := by
        calc polar Q (σ gs (θ y₀ : Fin d → K)) (y' : Fin d → K)
            = polar Q (σ gs (θ y₀ : Fin d → K)) (σ gs (y'' : Fin d → K)) := by
                rw [hσy'']
          _ = (multiplier Q gsp : K) *
                g.right (polar Q (θ y₀ : Fin d → K) (y'' : Fin d → K)) :=
              polar_coordinateSemilinearMap (g := gsp) _ _
          _ = (multiplier Q gsp : K) *
                (-(2 : K)⁻¹ * g.right (polar Q (y₀ : Fin d → K) (y'' : Fin d → K))) := by
              rw [hθ y₀ y'', map_mul, hφ2]
          _ = -(2 : K)⁻¹ * (multiplier Q gsp : K) *
                g.right (polar Q (y₀ : Fin d → K) (y'' : Fin d → K)) := by ring
          _ = -(2 : K)⁻¹ * polar Q (σ gs (y₀ : Fin d → K)) (σ gs (y'' : Fin d → K)) := by
              rw [polar_coordinateSemilinearMap (g := gsp)]
              ring
          _ = -(2 : K)⁻¹ * polar Q (z : Fin d → K) (y' : Fin d → K) := by rw [hσy'']
          _ = polar Q (θ z : Fin d → K) (y' : Fin d → K) := (hθ z y').symm
      simpa [p, LinearMap.comp_apply, polarBilin_apply_apply] using hcalc
    exact congrArg Subtype.val hw1
  simp only [Y, Submodule.mem_map]
  refine ⟨z, Submodule.mem_top, ?_⟩
  rw [hφ_apply]
  rw [show (coordinateSemilinearMap g) (φ y₀) =
      (coordinateSemilinearMap g) ((y₀ : Fin d → K) + (θ y₀ : Fin d → K)) from by rw [hφ_apply]]
  rw [map_add, hθnat]

end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

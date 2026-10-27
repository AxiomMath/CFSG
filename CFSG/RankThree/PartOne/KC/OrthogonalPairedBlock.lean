module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockUpdate
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Restriction

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem supportedBlock_le_centralizer (h : K[X]) :
    supportedBlock Q x h ≤ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := fun _ hg =>
  (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).2

theorem supportedBlock_le_isometryCentralizer (h : K[X]) :
    supportedBlock Q x h ≤ isometryCentralizer Q x := fun _ hg => (Subgroup.mem_inf.mp hg).1

@[expose] noncomputable def centralizerGL (x : V ≃ₗ[K] V) (h : K[X]) :
    ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) →* BlockGL x h :=
  (Units.map (commutantRestrictHom (x := x.toLinearMap) h).toMonoidHom).comp
    (centralizerUnits x).toMonoidHom

theorem coe_centralizerGL (x : V ≃ₗ[K] V) (h : K[X])
    (g : ↥(Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))))
    (v : primaryComponent x.toLinearMap h) :
    (((centralizerGL x h g : BlockGL x h) : Module.End (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)) v : V) = g.1 (v : V) := rfl

@[expose] noncomputable def blockGL (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X]) :
    ↥(supportedBlock Q x h) →* BlockGL x h :=
  (centralizerGL x h).comp (Subgroup.inclusion (supportedBlock_le_centralizer h))

theorem coe_blockGL (h : K[X]) (g : ↥(supportedBlock Q x h))
    (v : primaryComponent x.toLinearMap h) :
    (((blockGL Q x h g : BlockGL x h) : Module.End (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)) v : V) = g.1 (v : V) := rfl

end Restriction

section RestrictionInj

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.eq_one_of_blockGL_eq_one (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {c : ↥(supportedBlock Q x h)}
    (hc : blockGL Q x h c = 1) : c = 1 := by
  have hh' := hx.reciprocalPolynomial_mem hh
  have hcc := (supportedBlock_le_centralizer h) c.2
  have hcO := (supportedBlock_le_isometryCentralizer h) c.2
  have h1 : ∀ u ∈ primaryComponent x.toLinearMap h, c.1 u = u := fun u hu => by
    have := congrArg (fun γ : BlockGL x h => ((γ : Module.End (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)) ⟨u, hu⟩ : V)) hc
    exact this
  have h2 : ∀ w ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h), c.1 w = w := by
    intro w hw
    have hcw : c.1 w - w ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h) :=
      Submodule.sub_mem _ (apply_mem_primaryComponent_of_mem_centralizer hcc hw) hw
    have : c.1 w - w = 0 := by
      refine hx.eq_zero_of_polar_paired_right hh hcw fun u hu => ?_
      have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
        (Subgroup.mem_inf.mp hcO).1 u w
      rw [h1 u hu] at this
      rw [QuadraticMap.polar_sub_right, ← this, sub_self]
    exact sub_eq_zero.mp this
  have h3 : ∀ r ∈ othersSpace x.toLinearMap h, c.1 r = r := (mem_supportedBlock.mp c.2).2
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl (hx.isCompl_orbit_others hh) v
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
  show c.1 (u₁ + u₂ + r) = u₁ + u₂ + r
  rw [map_add, map_add, h1 u₁ hu₁, h2 u₂ hu₂, h3 r hr]

theorem OddOrderIsometry.blockGL_injective (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) : Function.Injective (blockGL Q x h) :=
  (injective_iff_map_eq_one _).mpr fun _ hc => hx.eq_one_of_blockGL_eq_one hh hc

end RestrictionInj

section ToBlockGL

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {x : V ≃ₗ[K] V}

@[expose] noncomputable def toEndE (a : K[X])
    (f : primaryComponent x.toLinearMap a →ₗ[K] primaryComponent x.toLinearMap a)
    (hf : Commute f (primaryRestrict x.toLinearMap a)) :
    Module.End (AdjoinRoot a) (primaryComponent x.toLinearMap a) where
  toFun := f
  map_add' := map_add f
  map_smul' e v := by
    induction e using AdjoinRoot.induction_on with
    | ih q =>
      have h1 := (commute_aeval hf q).eq
      have h2 : (AdjoinRoot.mk a q) • v = aeval (primaryRestrict x.toLinearMap a) q v := by
        rw [primaryComponent.smul_eq]; rfl
      have h3 : (AdjoinRoot.mk a q) • f v =
          aeval (primaryRestrict x.toLinearMap a) q (f v) := by
        rw [primaryComponent.smul_eq]; rfl
      simp only [RingHom.id_apply]
      rw [h2, h3]
      exact congrArg (fun T : Module.End K (primaryComponent x.toLinearMap a) => T v) h1

theorem toEndE_apply (a : K[X])
    (f : primaryComponent x.toLinearMap a →ₗ[K] primaryComponent x.toLinearMap a)
    (hf : Commute f (primaryRestrict x.toLinearMap a)) (v : primaryComponent x.toLinearMap a) :
    toEndE a f hf v = f v := rfl

@[expose] noncomputable def toBlockGL (a : K[X])
    (f : primaryComponent x.toLinearMap a ≃ₗ[K] primaryComponent x.toLinearMap a)
    (hf : ∀ v : primaryComponent x.toLinearMap a,
      f (primaryRestrict x.toLinearMap a v) = primaryRestrict x.toLinearMap a (f v)) :
    BlockGL x a where
  val := toEndE a f.toLinearMap (LinearMap.ext fun v => hf v)
  inv := toEndE a f.symm.toLinearMap (LinearMap.ext fun v => by
    apply f.injective
    show f (f.symm (primaryRestrict x.toLinearMap a v)) = f (primaryRestrict x.toLinearMap a
      (f.symm v))
    rw [f.apply_symm_apply, hf, f.apply_symm_apply])
  val_inv := LinearMap.ext fun v => f.apply_symm_apply v
  inv_val := LinearMap.ext fun v => f.symm_apply_apply v

theorem coe_toBlockGL (a : K[X])
    (f : primaryComponent x.toLinearMap a ≃ₗ[K] primaryComponent x.toLinearMap a)
    (hf : ∀ v : primaryComponent x.toLinearMap a,
      f (primaryRestrict x.toLinearMap a v) = primaryRestrict x.toLinearMap a (f v))
    (v : primaryComponent x.toLinearMap a) :
    (((toBlockGL a f hf : BlockGL x a) : Module.End (AdjoinRoot a)
      (primaryComponent x.toLinearMap a)) v) = f v := rfl

end ToBlockGL

section Adjoint

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

@[expose] noncomputable def pairingHom (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X]) :
    primaryComponent x.toLinearMap h →ₗ[K] primaryComponent x.toLinearMap (reciprocalPolynomial h)
      →ₗ[K] K :=
  (QuadraticMap.polarBilin Q).compl₁₂ (primaryComponent x.toLinearMap h).subtype
    (primaryComponent x.toLinearMap (reciprocalPolynomial h)).subtype

omit [FiniteDimensional K V] in
theorem pairingHom_apply (h : K[X]) (u : primaryComponent x.toLinearMap h)
    (w : primaryComponent x.toLinearMap (reciprocalPolynomial h)) :
    pairingHom Q x h u w = QuadraticMap.polar Q (u : V) (w : V) := rfl

theorem OddOrderIsometry.pairing_flip_bijective (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) :
    Function.Bijective (pairingHom Q x h).flip := by
  have hinj₂ : Function.Injective (pairingHom Q x h).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine Subtype.ext (hx.eq_zero_of_polar_paired_right hh w.2 fun u hu => ?_)
    simpa [pairingHom_apply] using LinearMap.congr_fun hw ⟨u, hu⟩
  have hinj₁ : Function.Injective (pairingHom Q x h) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_paired_left hh u.2 fun w hw => ?_)
    simpa [pairingHom_apply] using LinearMap.congr_fun hu ⟨w, hw⟩
  have hdim : finrank K (primaryComponent x.toLinearMap h) =
      finrank K (primaryComponent x.toLinearMap (reciprocalPolynomial h)) := by
    refine le_antisymm ?_ ?_
    · have := LinearMap.finrank_le_finrank_of_injective hinj₁
      rwa [Subspace.dual_finrank_eq] at this
    · have := LinearMap.finrank_le_finrank_of_injective hinj₂
      rwa [Subspace.dual_finrank_eq] at this
  refine ⟨hinj₂, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Subspace.dual_finrank_eq]; exact hdim.symm)).mp hinj₂

theorem OddOrderIsometry.exists_adjoint (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap)
    (φ : primaryComponent x.toLinearMap h →ₗ[K] primaryComponent x.toLinearMap h) :
    ∃ φ' : primaryComponent x.toLinearMap (reciprocalPolynomial h) →ₗ[K]
        primaryComponent x.toLinearMap (reciprocalPolynomial h),
      ∀ (u : primaryComponent x.toLinearMap h)
        (w : primaryComponent x.toLinearMap (reciprocalPolynomial h)),
        pairingHom Q x h (φ u) w = pairingHom Q x h u (φ' w) := by
  let Φ := LinearEquiv.ofBijective (pairingHom Q x h).flip (hx.pairing_flip_bijective hh)
  refine ⟨Φ.symm.toLinearMap ∘ₗ φ.dualMap ∘ₗ Φ.toLinearMap, fun u w => ?_⟩
  have h1 : (pairingHom Q x h).flip (Φ.symm (φ.dualMap (Φ w))) = φ.dualMap (Φ w) :=
    Φ.apply_symm_apply _
  have h2 := LinearMap.congr_fun h1 u
  simp only [LinearMap.flip_apply] at h2
  change _ = _ at h2
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [h2]
  rfl

omit [FiniteDimensional K V] in
theorem symm_apply_mem_primaryComponent {a : K[X]} {v : V}
    (hv : v ∈ primaryComponent x.toLinearMap a) : x.symm v ∈ primaryComponent x.toLinearMap a := by
  have hc : Commute x.symm.toLinearMap x.toLinearMap := by
    refine LinearMap.ext fun w => ?_
    simp
  exact apply_mem_primaryComponent hc hv

theorem OddOrderIsometry.exists_inverse_adjoint (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (γ : BlockGL x h) :
    ∃ δ : primaryComponent x.toLinearMap (reciprocalPolynomial h) ≃ₗ[K]
        primaryComponent x.toLinearMap (reciprocalPolynomial h),
      (∀ w, δ (primaryRestrict x.toLinearMap (reciprocalPolynomial h) w) =
        primaryRestrict x.toLinearMap (reciprocalPolynomial h) (δ w)) ∧
      ∀ (u : primaryComponent x.toLinearMap h)
        (w : primaryComponent x.toLinearMap (reciprocalPolynomial h)),
        pairingHom Q x h ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) u)
          (δ w) = pairingHom Q x h u w := by
  classical
  let φ : primaryComponent x.toLinearMap h →ₗ[K] primaryComponent x.toLinearMap h :=
    ((γ⁻¹ : BlockGL x h) : Module.End (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)).restrictScalars K
  let ψ : primaryComponent x.toLinearMap h →ₗ[K] primaryComponent x.toLinearMap h :=
    ((γ : BlockGL x h) : Module.End (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)).restrictScalars K
  have hψφ : ∀ u, ψ (φ u) = u := fun u => by
    have := congrArg (fun f : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h) => f u)
      γ.mul_inv
    exact this
  have hφψ : ∀ u, φ (ψ u) = u := fun u => by
    have := congrArg (fun f : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h) => f u)
      γ.inv_mul
    exact this
  have hφcomm : ∀ u, φ (primaryRestrict x.toLinearMap h u) =
      primaryRestrict x.toLinearMap h (φ u) := fun u => by
    have hr : ∀ v, primaryRestrict x.toLinearMap h v = AdjoinRoot.root h • v := fun v =>
      Subtype.ext (coe_root_smul_primaryComponent x.toLinearMap h v).symm
    rw [hr, hr]
    exact map_smul ((γ⁻¹ : BlockGL x h) : Module.End (AdjoinRoot h)
      (primaryComponent x.toLinearMap h)) (AdjoinRoot.root h) u
  obtain ⟨A, hA⟩ := hx.exists_adjoint hh φ
  obtain ⟨C, hC⟩ := hx.exists_adjoint hh ψ
  have hext : ∀ w₁ w₂ : primaryComponent x.toLinearMap (reciprocalPolynomial h),
      (∀ u : primaryComponent x.toLinearMap h,
        pairingHom Q x h u w₁ = pairingHom Q x h u w₂) → w₁ = w₂ := fun w₁ w₂ hw =>
    (hx.pairing_flip_bijective hh).1 (LinearMap.ext fun u => hw u)
  have hAC : ∀ w, A (C w) = w := fun w => hext _ _ fun u => by
    rw [← hA u (C w), ← hC (φ u) w, hψφ]
  have hCA : ∀ w, C (A w) = w := fun w => hext _ _ fun u => by
    rw [← hC u (A w), ← hA (ψ u) w, hφψ]
  refine ⟨LinearEquiv.ofLinearMap A C (LinearMap.ext hAC) (LinearMap.ext hCA), ?_, ?_⟩
  · intro w
    refine hext _ _ fun u => ?_
    show pairingHom Q x h u (A (primaryRestrict x.toLinearMap (reciprocalPolynomial h) w)) =
      pairingHom Q x h u (primaryRestrict x.toLinearMap (reciprocalPolynomial h) (A w))
    set u' : primaryComponent x.toLinearMap h :=
      ⟨x.symm (u : V), symm_apply_mem_primaryComponent u.2⟩ with hu'
    have hu'u : primaryRestrict x.toLinearMap h u' = u := Subtype.ext (by simp [hu'])
    have h1 : ((φ u' : primaryComponent x.toLinearMap h) : V) =
        x.symm ((φ u : primaryComponent x.toLinearMap h) : V) := by
      have : φ u = primaryRestrict x.toLinearMap h (φ u') := by rw [← hu'u, hφcomm]
      rw [this]
      simp
    calc pairingHom Q x h u (A (primaryRestrict x.toLinearMap (reciprocalPolynomial h) w))
        = pairingHom Q x h (φ u) (primaryRestrict x.toLinearMap (reciprocalPolynomial h) w) :=
          (hA u _).symm
      _ = QuadraticMap.polar Q ((φ u : primaryComponent x.toLinearMap h) : V) (x (w : V)) := rfl
      _ = QuadraticMap.polar Q (x.symm ((φ u : primaryComponent x.toLinearMap h) : V)) (w : V) :=
          (hx.polar_symm_apply _ _).symm
      _ = QuadraticMap.polar Q ((φ u' : primaryComponent x.toLinearMap h) : V) (w : V) := by
          rw [h1]
      _ = pairingHom Q x h (φ u') w := rfl
      _ = pairingHom Q x h u' (A w) := hA u' w
      _ = QuadraticMap.polar Q (x.symm (u : V)) ((A w : _) : V) := rfl
      _ = QuadraticMap.polar Q (u : V) (x ((A w : _) : V)) := hx.polar_symm_apply _ _
      _ = pairingHom Q x h u (primaryRestrict x.toLinearMap (reciprocalPolynomial h) (A w)) := rfl
  · intro u w
    show pairingHom Q x h (ψ u) (A w) = pairingHom Q x h u w
    rw [hC u (A w), hCA]

end Adjoint

section Surjective

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem polar_orbit_expand (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ reciprocalPolynomial h) {u₁ w₁ u₂ w₂ : V}
    (hu₁ : u₁ ∈ primaryComponent x.toLinearMap h) (hw₁ : w₁ ∈ primaryComponent x.toLinearMap h)
    (hu₂ : u₂ ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h))
    (hw₂ : w₂ ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h)) :
    QuadraticMap.polar Q (u₁ + u₂) (w₁ + w₂) =
      QuadraticMap.polar Q u₁ w₂ + QuadraticMap.polar Q u₂ w₁ := by
  rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
    hx.polar_eq_zero_of_ne hh hne hu₁ hw₁, hx.polar_reciprocal_eq_zero_of_ne hh hne hu₂ hw₂]
  ring

theorem OddOrderIsometry.blockGL_surjective_paired (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ reciprocalPolynomial h) :
    Function.Surjective (blockGL Q x h) := by
  classical
  intro γ
  obtain ⟨δ, hδcomm, hδ⟩ := hx.exists_inverse_adjoint hh γ
  have hh' := hx.reciprocalPolynomial_mem hh
  have hsq := hx.squarefree_minpoly
  have hne1 : h ≠ X - 1 := fun e => hne (by rw [e, reciprocalPolynomial_X_sub_one])
  let a : primaryFactors x.toLinearMap := ⟨h, hh⟩
  let a' : primaryFactors x.toLinearMap := ⟨reciprocalPolynomial h, hh'⟩
  have haa' : a' ≠ a := fun e => hne (congrArg Subtype.val e).symm
  let T₁ := blockUpdate hsq a γ
  let δ' : BlockGL x a' := toBlockGL (reciprocalPolynomial h) δ hδcomm
  let T₂ := blockUpdate hsq a' δ'
  have hT : (T₁ * T₂).1 ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (T₁ * T₂).2
  have hgU : ∀ u : primaryComponent x.toLinearMap h, (T₁ * T₂).1 (u : V) =
      ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) u : V) := by
    intro u
    show T₁.1 (T₂.1 (u : V)) = _
    rw [blockUpdate_apply_ne hsq a' a haa'.symm δ' u]
    exact blockUpdate_apply_self hsq a γ u
  have hgU' : ∀ w : primaryComponent x.toLinearMap (reciprocalPolynomial h),
      (T₁ * T₂).1 (w : V) = (δ w : V) := by
    intro w
    show T₁.1 (T₂.1 (w : V)) = _
    rw [blockUpdate_apply_self hsq a' δ' w]
    exact blockUpdate_apply_ne hsq a a' haa' γ (δ w)
  have hmem : (T₁ * T₂).1 ∈ supportedBlock Q x h := by
    refine hx.mem_supportedBlock_of_block hh hT ?_ ?_
    · refine fixes_othersSpace_iff.mpr fun k hk hkh hkh' v hv => ?_
      have hka : (⟨k, hk⟩ : primaryFactors x.toLinearMap) ≠ a :=
        fun e => hkh (congrArg Subtype.val e)
      have hka' : (⟨k, hk⟩ : primaryFactors x.toLinearMap) ≠ a' :=
        fun e => hkh' (congrArg Subtype.val e)
      show T₁.1 (T₂.1 v) = v
      have h2 := blockUpdate_apply_ne hsq a' ⟨k, hk⟩ hka' δ' ⟨v, hv⟩
      have h1 := blockUpdate_apply_ne hsq a ⟨k, hk⟩ hka γ ⟨v, hv⟩
      simp only at h1 h2
      rw [h2, h1]
    · intro u hu
      refine hx.quadratic_eq_of_polar_eq hh hne1 hT (fun u hu u' hu' => ?_) hu
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hu'
      rw [map_add, map_add, hgU ⟨u₁, hu₁⟩, hgU ⟨w₁, hw₁⟩, hgU' ⟨u₂, hu₂⟩, hgU' ⟨w₂, hw₂⟩]
      rw [polar_orbit_expand hx hh hne hu₁ hw₁ hu₂ hw₂]
      rw [polar_orbit_expand hx hh hne
        ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) ⟨u₁, hu₁⟩).2
        ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) ⟨w₁, hw₁⟩).2
        (δ ⟨u₂, hu₂⟩).2 (δ ⟨w₂, hw₂⟩).2]
      have e1 := hδ ⟨u₁, hu₁⟩ ⟨w₂, hw₂⟩
      have e2 := hδ ⟨w₁, hw₁⟩ ⟨u₂, hu₂⟩
      rw [pairingHom_apply, pairingHom_apply] at e1 e2
      rw [e1, QuadraticMap.polar_comm _ (δ ⟨u₂, hu₂⟩ : V), e2, QuadraticMap.polar_comm Q (w₁ : V)]
  refine ⟨⟨(T₁ * T₂).1, hmem⟩, ?_⟩
  refine Units.ext (LinearMap.ext fun v => Subtype.ext ?_)
  exact hgU v

theorem OddOrderIsometry.blockGL_bijective_paired (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ reciprocalPolynomial h) :
    Function.Bijective (blockGL Q x h) :=
  ⟨hx.blockGL_injective hh, hx.blockGL_surjective_paired hh hne⟩

@[expose] noncomputable def pairedBlockEquiv (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ reciprocalPolynomial h) :
    ↥(supportedBlock Q x h) ≃* BlockGL x h :=
  MulEquiv.ofBijective (blockGL Q x h) (hx.blockGL_bijective_paired hh hne)

end Surjective

end CFSG.RankThree.PartOne.KCOrthogonal

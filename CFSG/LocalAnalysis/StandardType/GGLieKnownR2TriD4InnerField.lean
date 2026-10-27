module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4InnerActionChar
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TriD4InnerActionTorus

public section

namespace CFSG.StandardType.LieKnownR2.TriD4.Inner

open CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.SeitzReduction
open scoped commutatorElement

private theorem tfield_normalizer_map {C : Type*} [Group C] {X : Subgroup C} {f : MulAut C}
    (hf : X.map f.toMonoidHom = X) {n : C} (hn : n ∈ Subgroup.normalizer X) :
    f n ∈ Subgroup.normalizer X := by
  have hfx : ∀ z : C, f z ∈ X ↔ z ∈ X := by
    intro z
    constructor
    · intro hz
      have hz' : f z ∈ X.map f.toMonoidHom := by rw [hf]; exact hz
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 hz'
      rwa [f.injective hyz] at hy
    · intro hz
      rw [← hf]
      exact Subgroup.mem_map.2 ⟨z, hz, rfl⟩
  have hfinv : ∀ z : C, f⁻¹ z ∈ X ↔ z ∈ X := by
    intro z
    have := hfx (f⁻¹ z)
    simpa using this.symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : f n * x * (f n)⁻¹ = f (n * f⁻¹ x * n⁻¹) := by
    rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]
  rw [key, hfx]
  rw [← (Subgroup.mem_normalizer_iff.mp hn (f⁻¹ x)), hfinv]

private theorem tfield_coe_xPar_highRoot
    {K : Type} [Field K] (c : K) :
    ((xPar (rootOperatorFamily d4) (highRoot d4) c : adjointGroup d4 K) : ModGL d4 K) =
      pinnedX d4 K (highRoot d4)
        (((rootOperatorFamily d4).pinnedFamilySign (highRoot d4) : K) * c) := by
  have h2 : pinnedX d4 K (highRoot d4)
        (((rootOperatorFamily d4).pinnedFamilySign (highRoot d4) : K) * c) =
      (rootOperatorFamily d4).eltUnit K ⟨highRoot d4, isRoot_highRoot d4⟩ c := by
    rw [(rootOperatorFamily d4).pinnedX_eq_eltUnit K (isRoot_highRoot d4)]
    rw [← mul_assoc, (rootOperatorFamily d4).pinnedFamilySign_mul_self, one_mul]
  rw [xPar_of_isRoot (isRoot_highRoot d4)]
  exact h2.symm

private theorem tfield_X_mem
    {K : Type} [Field K] (σ : K ≃+* K) (t : fixedField σ.toRingHom) :
    (↑(triD4C0Xtheta σ t) : ModGL d4 K) ∈ rootSubgroup d4 K (highRoot d4) ⊓
      twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [show (↑(triD4C0Xtheta σ t) : ModGL d4 K) = pinnedX d4 K (highRoot d4)
        (((rootOperatorFamily d4).pinnedFamilySign (highRoot d4) : K) * (t : K))
        from tfield_coe_xPar_highRoot (t : K)]
    exact CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨_, rfl⟩
  · exact graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom (triD4C0Xtheta σ t).2

private theorem tfield_Xtheta_mem_highRoot
    {K : Type} [Field K] (σ : K ≃+* K) (t : fixedField σ.toRingHom) :
    triD4C0Xtheta σ t ∈ Bridge.triD4C0HighRoot K σ.toRingHom := by
  rw [show Bridge.triD4C0HighRoot K σ.toRingHom =
      (rootSubgroup d4 K (highRoot d4) ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) from rfl]
  exact Subgroup.mem_subgroupOf.mpr (tfield_X_mem σ t)

private theorem tfield_fieldActor_maps_highRoot_le
    {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) :
    (Bridge.triD4C0HighRoot K σ.toRingHom).map
        (fieldActor (t := TwistTag.D4) σ δ).toMonoidHom ≤
      Bridge.triD4C0HighRoot K σ.toRingHom := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  rw [show Bridge.triD4C0HighRoot K σ.toRingHom =
      (rootSubgroup d4 K (highRoot d4) ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) from rfl]
  rw [Subgroup.mem_subgroupOf]
  have hxinf : ((x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL d4 K) ∈
      rootSubgroup d4 K (highRoot d4) ⊓ twistedFixedGroup TwistTag.D4 K σ.toRingHom := by
    rw [← Subgroup.mem_subgroupOf (K := graphFixedRootGroup TwistTag.D4 K σ.toRingHom)]
    exact hx
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · change (((fieldActor (t := TwistTag.D4) σ δ) x :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL d4 K) ∈
      rootSubgroup d4 K (highRoot d4)
    obtain ⟨c, hc⟩ := CFSG.Blueprint.Chevalley.mem_rootSubgroup.1 (Subgroup.mem_inf.1 hxinf).1
    have hcoe := coe_fieldActor (t := TwistTag.D4) σ δ x
    rw [hcoe, ← hc]
    exact CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨δ c, by
      rw [show Units.map (entrywiseHom δ.toRingHom) (pinnedX d4 K (highRoot d4) c) =
          pinnedX d4 K (highRoot d4) (δ c) from
        Units.ext (entrywise_pinnedX δ.toRingHom (highRoot d4) c)]⟩
  · exact graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom
      ((fieldActor (t := TwistTag.D4) σ δ) x).2

private theorem tfield_fieldActor_map_highRoot_eq
    {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) :
    (Bridge.triD4C0HighRoot K σ.toRingHom).map
        (fieldActor (t := TwistTag.D4) σ δ).toMonoidHom =
      Bridge.triD4C0HighRoot K σ.toRingHom := by
  apply le_antisymm (tfield_fieldActor_maps_highRoot_le σ δ)
  have hfinv : (fieldActor (t := TwistTag.D4) σ δ)⁻¹ = fieldActor (t := TwistTag.D4) σ δ⁻¹ := by
    rw [← fieldActorHom_apply (t := TwistTag.D4) σ δ,
        ← fieldActorHom_apply (t := TwistTag.D4) σ δ⁻¹, map_inv]
  have hle_inv : (Bridge.triD4C0HighRoot K σ.toRingHom).map
      ((fieldActor (t := TwistTag.D4) σ δ)⁻¹).toMonoidHom ≤
      Bridge.triD4C0HighRoot K σ.toRingHom := by
    rw [hfinv]
    exact tfield_fieldActor_maps_highRoot_le σ δ⁻¹
  intro x hx
  have hx' : (fieldActor (t := TwistTag.D4) σ δ)⁻¹ x ∈
      Bridge.triD4C0HighRoot K σ.toRingHom :=
    hle_inv (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  exact Subgroup.mem_map.2 ⟨(fieldActor (t := TwistTag.D4) σ δ)⁻¹ x, hx',
    MulAut.apply_inv_self _ (fieldActor (t := TwistTag.D4) σ δ) x⟩

private theorem tfield_triD4C0Xtheta_injective
    {K : Type} [Field K] (σ : K ≃+* K) :
    Function.Injective (triD4C0Xtheta (K := K) σ) := by
  intro a b hab
  have hmod : ((xPar (rootOperatorFamily d4) (highRoot d4) (a : K) :
        adjointGroup d4 K) : ModGL d4 K) =
      ((xPar (rootOperatorFamily d4) (highRoot d4) (b : K) :
        adjointGroup d4 K) : ModGL d4 K) :=
    congrArg (fun z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom => (z : ModGL d4 K)) hab
  have hadj : (xPar (rootOperatorFamily d4) (highRoot d4) (a : K) : adjointGroup d4 K) =
      (xPar (rootOperatorFamily d4) (highRoot d4) (b : K) : adjointGroup d4 K) :=
    Subtype.ext hmod
  exact Subtype.ext (xPar_injective (isRoot_highRoot d4) hadj)

theorem triD4_delta_fixes_k
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {δ : K ≃+* K} {g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hα : α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ)
    (hX : (Bridge.triD4C0HighRoot K σ.toRingHom).map α.toMonoidHom =
      Bridge.triD4C0HighRoot K σ.toRingHom)
    (hO : ∀ n ∈ Subgroup.normalizer (Bridge.triD4C0HighRoot K σ.toRingHom :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      α n * n⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (Bridge.triD4C0HighRoot K σ.toRingHom :
        Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))) :
    ∀ c : K, σ c = c → δ c = c := by
  intro c hc
  by_cases hc0 : c = 0
  · rw [hc0, map_zero]
  let X := Bridge.triD4C0HighRoot K σ.toRingHom
  let C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  let f : MulAut C := fieldActor (t := TwistTag.D4) σ δ
  have hfa_eq : X.map f.toMonoidHom = X := tfield_fieldActor_map_highRoot_eq σ δ
  have hfaX : ∀ z : C, f z ∈ X ↔ z ∈ X := by
    intro z
    constructor
    · intro hz
      have hz' : f z ∈ X.map f.toMonoidHom := by rw [hfa_eq]; exact hz
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 hz'
      rwa [f.injective hyz] at hy
    · intro hz
      exact hfa_eq ▸ Subgroup.mem_map.2 ⟨z, hz, rfl⟩
  have hfaXinv : ∀ z : C, f⁻¹ z ∈ X ↔ z ∈ X := by
    intro z
    have := hfaX (f⁻¹ z)
    simpa using this.symm
  have hαX : ∀ z : C, α z ∈ X ↔ z ∈ X := by
    intro z
    constructor
    · intro hz
      have hz' : α z ∈ X.map α.toMonoidHom := by rw [hX]; exact hz
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 hz'
      rwa [α.injective hyz] at hy
    · intro hz
      have hz' : α z ∈ X.map α.toMonoidHom := Subgroup.mem_map.2 ⟨z, hz, rfl⟩
      rwa [hX] at hz'
  have hgN : g ∈ Subgroup.normalizer (X : Set C) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : g * x * g⁻¹ = α (f⁻¹ x) := by
      rw [hα, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.conj_apply]
    rw [key, hαX, hfaXinv]
  have hc' : c ∈ fixedField σ.toRingHom := by
    rw [show fixedField σ.toRingHom =
        RingHom.eqLocusField σ.toRingHom (RingHom.id K) from rfl]
    exact RingHom.mem_eqLocusField.mpr (by simpa using hc)
  let γ : (fixedField σ.toRingHom)ˣ :=
    Units.mk0 ⟨c, hc'⟩ (by intro h; exact hc0 (congrArg Subtype.val h))
  obtain ⟨n, hn, hnact⟩ := triD4_exists_torus_action σ hσ3 hf hK hσ γ
  let m : C := f n
  have hmN : m ∈ Subgroup.normalizer (X : Set C) := tfield_normalizer_map hfa_eq hn
  have hd : α n * n⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (X : Set C)) := hO n hn
  have hdcent : α n * n⁻¹ ∈ Subgroup.centralizer (X : Set C) :=
    triD4_pCore_le_centralizer σ hd
  have hrel : ∀ x ∈ X, (α n) * x * (α n)⁻¹ = n * x * n⁻¹ := by
    intro x hx
    set d := α n * n⁻¹ with hddef
    have hcomm : ∀ y ∈ X, y * d = d * y := fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hdcent) y hy
    have hαn : α n = d * n := by rw [hddef]; group
    have hnx : n * x * n⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hn x).mp hx
    calc (α n) * x * (α n)⁻¹ = d * (n * x * n⁻¹) * d⁻¹ := by rw [hαn]; group
      _ = n * x * n⁻¹ := by rw [← hcomm (n * x * n⁻¹) hnx]; group
  obtain ⟨μ, hμ⟩ := triD4_normalizer_actionChar σ hσ3 hgN
  obtain ⟨ν, hν⟩ := triD4_normalizer_actionChar σ hσ3 hmN
  have hxθ_mem : ∀ t : fixedField σ.toRingHom, triD4C0Xtheta σ t ∈ X :=
    fun t => tfield_Xtheta_mem_highRoot σ t
  have hμinv : ∀ t : fixedField σ.toRingHom,
      g⁻¹ * triD4C0Xtheta σ t * g = triD4C0Xtheta σ (μ⁻¹ * t) := by
    intro t
    have h := hμ (μ⁻¹ * t)
    rw [show μ * (μ⁻¹ * t) = t from by
      rw [← mul_assoc, Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero μ),
        one_mul]] at h
    rw [← h]
    group
  have hαn_eq : α n = g * m * g⁻¹ := by
    rw [hα, MulAut.mul_apply, MulAut.conj_apply]
  have hstep : ∀ t : fixedField σ.toRingHom,
      (α n) * triD4C0Xtheta σ t * (α n)⁻¹ = triD4C0Xtheta σ (ν * t) := by
    intro t
    calc (α n) * triD4C0Xtheta σ t * (α n)⁻¹
        = g * m * (g⁻¹ * triD4C0Xtheta σ t * g) * m⁻¹ * g⁻¹ := by rw [hαn_eq]; group
      _ = g * m * triD4C0Xtheta σ (μ⁻¹ * t) * m⁻¹ * g⁻¹ := by rw [hμinv t]
      _ = g * (m * triD4C0Xtheta σ (μ⁻¹ * t) * m⁻¹) * g⁻¹ := by group
      _ = g * triD4C0Xtheta σ (ν * (μ⁻¹ * t)) * g⁻¹ := by rw [hν]
      _ = triD4C0Xtheta σ (μ * (ν * (μ⁻¹ * t))) := by rw [hμ]
      _ = triD4C0Xtheta σ (ν * t) := by
          congr 1
          rw [show μ * (ν * (μ⁻¹ * t)) = ν * (μ * (μ⁻¹ * t)) from by ring,
            Units.val_inv_eq_inv_val, mul_inv_cancel_left₀ (Units.ne_zero μ)]
  have hstep2 : ∀ t : fixedField σ.toRingHom,
      (α n) * triD4C0Xtheta σ t * (α n)⁻¹ = n * triD4C0Xtheta σ t * n⁻¹ :=
    fun t => hrel (triD4C0Xtheta σ t) (hxθ_mem t)
  have hνγ : (ν : K) = (γ : K) := by
    have h1 : ∀ t : fixedField σ.toRingHom,
        triD4C0Xtheta σ (ν * t) = triD4C0Xtheta σ (γ * t) := by
      intro t
      rw [← hstep t, hstep2 t, hnact t]
    have h := h1 1
    simp only [mul_one] at h
    exact congrArg (fun u : fixedField σ.toRingHom => (u : K))
      (tfield_triD4C0Xtheta_injective σ h)
  have hdeltat : ∀ t : fixedField σ.toRingHom, σ (δ (t : K)) = δ (t : K) := fun t => by
    change σ (δ (t : K)) = δ (t : K)
    rw [← ringEquiv_comm_of_finite σ δ (t : K)]
    exact congrArg δ (show σ (t : K) = (t : K) from t.2)
  have hT1 : ∀ t : fixedField σ.toRingHom,
      f (triD4C0Xtheta σ t) = triD4C0Xtheta σ ⟨δ (t : K), hdeltat t⟩ := by
    intro t
    rw [fieldActor_triD4C0Xtheta]
  have h2eq : ∀ t : fixedField σ.toRingHom,
      m * f (triD4C0Xtheta σ t) * m⁻¹ = f (triD4C0Xtheta σ (γ * t)) := by
    intro t
    have h := congrArg f (hnact t)
    rwa [map_mul, map_mul, map_inv] at h
  have h4 : ∀ t : fixedField σ.toRingHom,
      m * f (triD4C0Xtheta σ t) * m⁻¹ =
        triD4C0Xtheta σ (ν * ⟨δ (t : K), hdeltat t⟩) := by
    intro t
    rw [hT1 t]
    exact hν ⟨δ (t : K), hdeltat t⟩
  have h5 : ∀ t : fixedField σ.toRingHom,
      triD4C0Xtheta σ (ν * ⟨δ (t : K), hdeltat t⟩) =
        triD4C0Xtheta σ ⟨δ (((γ * t : fixedField σ.toRingHom) : K)), hdeltat (γ * t)⟩ := by
    intro t
    rw [← h4 t, h2eq t, hT1 (γ * t)]
  have hfinal : δ (γ : K) = (γ : K) := by
    have h5one := h5 1
    have hL : (⟨δ ((1 : fixedField σ.toRingHom) : K), hdeltat 1⟩ :
        fixedField σ.toRingHom) = 1 := Subtype.ext (by simp)
    have hR : (⟨δ (((γ * 1 : fixedField σ.toRingHom) : K)), hdeltat (γ * 1)⟩ :
        fixedField σ.toRingHom) = ⟨δ (γ : K), hdeltat γ⟩ :=
      Subtype.ext (by rw [mul_one])
    rw [hL, mul_one, hR] at h5one
    have hinj := tfield_triD4C0Xtheta_injective σ h5one
    have hval : (ν : K) = δ (γ : K) := congrArg Subtype.val hinj
    rw [← hval, hνγ]
  rw [← show (γ : K) = c from rfl]
  exact hfinal

theorem triD4_delta_eq_one_of_fixes_k
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {δ : K ≃+* K} (hfix : ∀ c : K, σ c = c → δ c = c)
    (h2 : ∃ n : ℕ, δ ^ 2 ^ n = 1) : δ = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card K Nat.prime_two hK3
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  haveI : Module.Finite (ZMod 2) K := Module.Finite.of_finite
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    haveI : Fintype K := Fintype.ofFinite K
    change σ (σ (σ c)) = c
    rw [hσ (σ (σ c)), hσ (σ c), hσ c, ← pow_mul, ← pow_mul]
    have hexp : 2 ^ f * (2 ^ f * 2 ^ f) = Nat.card K := by
      rw [show 2 ^ f * (2 ^ f * 2 ^ f) = (2 ^ f) ^ 3 from by ring, ← hK]
    rw [hexp, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  let e : (K ≃+* K) ≃* (K ≃ₐ[ZMod 2] K) :=
    CFSG.Semidihedral.FixedFieldData.primeFieldAutEquiv 2 K
  have hmem : e δ ∈ (IntermediateField.fixedField (Subgroup.zpowers (e σ))).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact hfix x (hx (e σ) (Subgroup.mem_zpowers _))
  have hsub : e δ ∈ Subgroup.zpowers (e σ) := by
    rwa [IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers (e σ))] at hmem
  have hdvd : orderOf δ ∣ 3 := by
    have h1 : Subgroup.zpowers (e δ) ≤ Subgroup.zpowers (e σ) :=
      Subgroup.zpowers_le.mpr hsub
    have h2' : Nat.card (Subgroup.zpowers (e δ)) ∣ Nat.card (Subgroup.zpowers (e σ)) :=
      Subgroup.card_dvd_of_le h1
    have hordδ : orderOf (e δ) = orderOf δ :=
      orderOf_injective e.toMonoidHom e.injective δ
    have hordσ : orderOf (e σ) = orderOf σ :=
      orderOf_injective e.toMonoidHom e.injective σ
    rw [Nat.card_zpowers, Nat.card_zpowers, hordδ, hordσ] at h2'
    exact h2'.trans (orderOf_dvd_of_pow_eq_one hσ3)
  obtain ⟨n, hn⟩ := h2
  have hdvd2 : orderOf δ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime 3 (2 ^ n) :=
    Nat.Coprime.pow_right n (by decide : Nat.Coprime 3 2)
  have hone : orderOf δ = 1 := by
    have hgd : orderOf δ ∣ Nat.gcd 3 (2 ^ n) := Nat.dvd_gcd hdvd hdvd2
    rw [hcop.gcd_eq_one] at hgd
    exact Nat.dvd_one.mp hgd
  exact orderOf_eq_one_iff.mp hone

end CFSG.StandardType.LieKnownR2.TriD4.Inner

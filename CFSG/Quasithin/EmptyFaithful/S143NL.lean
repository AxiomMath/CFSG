module

public import CFSG.Quasithin.EmptyFaithful.S1422Extra

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace S143

@[expose] def ExtQ8SqS3S3 (P : Type*) [Group P] : Prop :=
  ∃ ψ : P →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), Function.Surjective ψ ∧ IsQ8Sq ↥ψ.ker ∧
    ∀ x : P, (∀ n ∈ ψ.ker, x * n = n * x) → x ∈ ψ.ker

section Assembly

variable {G : Type*} [Group G] {Gc : Type*} [Group Gc]

theorem ext_of_data {Gd CH U : Subgroup G} (φ : ↥Gd →* Gc) {δ : G}
    (hCHGd : CH ≤ Gd) (hUCH : U ≤ CH)
    (hker : ∀ x : ↥Gd, φ x = 1 ↔ (x : G) ∈ Subgroup.zpowers δ)
    (f : ↥CH →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hfδ : ∀ x : ↥CH, (x : G) ∈ Subgroup.zpowers δ → f x = 1)
    (hfU : ∀ x : ↥CH, (x : G) ∈ U → f x = 1)
    (hfker : ∀ x : ↥CH, f x = 1 → ∃ u ∈ U, ∃ w ∈ Subgroup.zpowers δ, (x : G) = u * w)
    (hUδ : ∀ u ∈ U, u ∈ Subgroup.zpowers δ → u = 1)
    (hUN : ∀ x ∈ CH, ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (hcen : ∀ x : ↥CH, (∀ u ∈ U, (x : G) * u = u * (x : G)) → f x = 1)
    (hU : IsQ8Sq ↥U) :
    ExtQ8SqS3S3 ↥((CH.subgroupOf Gd).map φ) := by
  set Y : Subgroup ↥Gd := CH.subgroupOf Gd with hY
  set φ' : ↥Y →* ↥(Y.map φ) := φ.subgroupMap Y with hφ'
  have hφ's : Function.Surjective φ' := MonoidHom.subgroupMap_surjective φ Y
  let ε : ↥Y ≃* ↥CH := Subgroup.subgroupOfEquivOfLe hCHGd
  have hεval : ∀ y : ↥Y, ((ε y : ↥CH) : G) = (((y : ↥Gd)) : G) := fun y => rfl
  let f' : ↥Y →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) := f.comp ε.toMonoidHom
  have hφ'val : ∀ y : ↥Y, ((φ' y : ↥(Y.map φ)) : Gc) = φ (y : ↥Gd) := fun y => rfl
  have hle : φ'.ker ≤ f'.ker := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy ⊢
    have h1 : φ (y : ↥Gd) = 1 := by
      have := congrArg Subtype.val hy
      exact this
    have h2 := (hker _).mp h1
    exact hfδ (ε y) h2
  let ψ : ↥(Y.map φ) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
    (MonoidHom.liftOfSurjective φ' hφ's) ⟨f', hle⟩
  have hψ : ∀ y : ↥Y, ψ (φ' y) = f' y := fun y =>
    MonoidHom.liftOfRightInverse_comp_apply φ' _ (Function.rightInverse_surjInv hφ's) ⟨f', hle⟩ y
  have hψs : Function.Surjective ψ := by
    intro b
    obtain ⟨x, hx⟩ := hf b
    refine ⟨φ' (ε.symm x), ?_⟩
    rw [hψ]
    show f (ε (ε.symm x)) = b
    rw [MulEquiv.apply_symm_apply]
    exact hx
  let ιU : ↥U →* ↥Y := (ε.symm : ↥CH →* ↥Y).comp (Subgroup.inclusion hUCH)
  have hιU : ∀ u : ↥U, ((((ιU u : ↥Y) : ↥Gd)) : G) = (u : G) := fun u => rfl
  have hΘker : ∀ u : ↥U, ψ (φ' (ιU u)) = 1 := by
    intro u
    rw [hψ]
    show f (ε (ε.symm (Subgroup.inclusion hUCH u))) = 1
    rw [MulEquiv.apply_symm_apply]
    exact hfU _ u.2
  let Θ : ↥U →* ↥ψ.ker :=
    (φ'.comp ιU).codRestrict ψ.ker (fun u => MonoidHom.mem_ker.mpr (hΘker u))
  have hΘinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : φ' (ιU u) = 1 := congrArg Subtype.val hu
    have h2 : φ ((ιU u : ↥Y) : ↥Gd) = 1 := congrArg Subtype.val h1
    have h3 := (hker _).mp h2
    rw [hιU] at h3
    exact Subtype.ext (hUδ _ u.2 h3)
  have hΘsurj : Function.Surjective Θ := by
    rintro ⟨p, hp⟩
    obtain ⟨y, rfl⟩ := hφ's p
    have h1 : f (ε y) = 1 := by
      have := MonoidHom.mem_ker.mp hp
      rw [hψ] at this
      exact this
    obtain ⟨u, hu, w, hw, hxuw⟩ := hfker (ε y) h1
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    show φ' (ιU ⟨u, hu⟩) = φ' y
    have hz : φ' ((ιU ⟨u, hu⟩)⁻¹ * y) = 1 := by
      apply Subtype.ext
      show φ ((((ιU ⟨u, hu⟩)⁻¹ * y : ↥Y)) : ↥Gd) = 1
      rw [hker]
      have e : ((((ιU ⟨u, hu⟩)⁻¹ * y : ↥Y) : ↥Gd) : G) = u⁻¹ * ((y : ↥Gd) : G) := rfl
      rw [e]
      have : ((y : ↥Gd) : G) = u * w := hxuw
      rw [this, inv_mul_cancel_left]
      exact hw
    rw [map_mul, map_inv] at hz
    exact (inv_mul_eq_one.mp hz)
  let eΘ : ↥U ≃* ↥ψ.ker := MulEquiv.ofBijective Θ ⟨hΘinj, hΘsurj⟩
  refine ⟨ψ, hψs, IsQ8Sq.of_mulEquiv eΘ hU, ?_⟩
  intro p hp
  obtain ⟨y, rfl⟩ := hφ's p
  rw [MonoidHom.mem_ker, hψ]
  apply hcen (ε y)
  intro u hu
  have hn := hp (φ' (ιU ⟨u, hu⟩)) (MonoidHom.mem_ker.mpr (hΘker ⟨u, hu⟩))
  have hn' : φ' (y * ιU ⟨u, hu⟩ * (ιU ⟨u, hu⟩ * y)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_mul, hn, mul_inv_cancel]
  have hmem : (((y * ιU ⟨u, hu⟩ * (ιU ⟨u, hu⟩ * y)⁻¹ : ↥Y) : ↥Gd) : G) ∈ Subgroup.zpowers δ := by
    apply (hker _).mp
    exact congrArg Subtype.val hn'
  have e : (((y * ιU ⟨u, hu⟩ * (ιU ⟨u, hu⟩ * y)⁻¹ : ↥Y) : ↥Gd) : G) =
      ((y : ↥Gd) : G) * u * ((y : ↥Gd) : G)⁻¹ * u⁻¹ := by
    show ((y : ↥Gd) : G) * u * (u * ((y : ↥Gd) : G))⁻¹ = _
    group
  rw [e] at hmem
  have hyCH : ((y : ↥Gd) : G) ∈ CH := Subgroup.mem_subgroupOf.mp y.2
  have hU1 : ((y : ↥Gd) : G) * u * ((y : ↥Gd) : G)⁻¹ * u⁻¹ ∈ U :=
    U.mul_mem (hUN _ hyCH u hu) (U.inv_mem hu)
  have h1 := hUδ _ hU1 hmem
  show ((y : ↥Gd) : G) * u = u * ((y : ↥Gd) : G)
  calc ((y : ↥Gd) : G) * u = (((y : ↥Gd) : G) * u * ((y : ↥Gd) : G)⁻¹ * u⁻¹) * (u * ((y : ↥Gd) : G)) := by
        group
    _ = u * ((y : ↥Gd) : G) := by rw [h1, one_mul]

end Assembly

end S143

end CFSG.Quasithin

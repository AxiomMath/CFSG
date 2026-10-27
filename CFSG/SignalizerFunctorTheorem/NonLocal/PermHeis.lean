module

public import CFSG.SignalizerFunctorTheorem.NonLocal.Heisenberg

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem exists_ne_of_translation {Γ ι F : Type*} [Group Γ] [Field F] (A Z : Subgroup Γ)
    (y : ι → Γ) (hcomm : ∀ i, ∀ a ∈ A, ⁅(y i)⁻¹, a⁆ ∈ Z)
    (hHD : ∀ i j, i ≠ j → ∀ u ∈ Z, ∃ a ∈ A, ⁅(y i)⁻¹, a⁆ = u * ⁅(y j)⁻¹, a⁆)
    (ξ : Γ → F) (hmul : ∀ z ∈ Z, ∀ z' ∈ Z, ξ (z * z') = ξ z * ξ z')
    (hne : ∀ z ∈ Z, ξ z ≠ 0) (hnt : ∃ z ∈ Z, ξ z ≠ 1) {i j : ι} (hij : i ≠ j) :
    ∃ a ∈ A, ξ ⁅(y i)⁻¹, a⁆ ≠ ξ ⁅(y j)⁻¹, a⁆ := by
  obtain ⟨u, hu, hξu⟩ := hnt
  obtain ⟨a, ha, hia⟩ := hHD i j hij u hu
  refine ⟨a, ha, ?_⟩
  rw [hia, hmul u hu _ (hcomm j a ha)]
  intro h
  exact hξu (mul_right_cancel₀ (hne _ (hcomm j a ha)) (by rw [one_mul]; exact h))

theorem card_le_finrank_of_heisenberg {F W G : Type*} [Field F] [AddCommGroup W] [Module F W]
    [Group G] [IsAlgClosed F] [FiniteDimensional F W] (ρ : G →* Module.End F W)
    (A Z : Subgroup G) (hA : IsMulCommutative A) [Finite A] (hinv : (Nat.card A : F) ≠ 0)
    (hZA : Z ≤ A) {ι : Type*} [Finite ι] (y : ι → G)
    (hcomm : ∀ i, ∀ a ∈ A, ⁅(y i)⁻¹, a⁆ ∈ Z)
    (hHD : ∀ i j, i ≠ j → ∀ u ∈ Z, ∃ a ∈ A, ⁅(y i)⁻¹, a⁆ = u * ⁅(y j)⁻¹, a⁆)
    (hnt : ∃ z ∈ Z, ρ z ≠ 1) :
    Nat.card ι ≤ Module.finrank F W :=
  card_le_finrank_of_translations ρ A Z hA hinv hZA y hcomm hnt
    fun ξ hmul hne hξ _ _ _ hij => exists_ne_of_translation A Z y hcomm hHD ξ hmul hne hξ hij

@[expose] def permFunHom (Λ : Type*) : Equiv.Perm Λ →* Module.End ℂ (Λ → ℂ) where
  toFun τ := LinearMap.funLeft ℂ ℂ (τ⁻¹ : Equiv.Perm Λ)
  map_one' := by
    refine LinearMap.ext fun f => funext fun x => ?_
    simp
  map_mul' τ υ := by
    refine LinearMap.ext fun f => funext fun x => ?_
    simp

@[simp]
theorem permFunHom_apply {Λ : Type*} (τ : Equiv.Perm Λ) (f : Λ → ℂ) (x : Λ) :
    permFunHom Λ τ f x = f (τ⁻¹ x) := rfl

theorem permFunHom_ne_one {Λ : Type*} {τ : Equiv.Perm Λ} (hτ : τ ≠ 1) : permFunHom Λ τ ≠ 1 := by
  classical
  intro h
  apply hτ
  ext x
  have h1 := congrFun (LinearMap.congr_fun h (Pi.single x (1 : ℂ))) x
  have h2 : (Pi.single x (1 : ℂ) : Λ → ℂ) (τ⁻¹ x) = 1 := by
    simpa using h1
  by_contra hx
  have h3 : τ⁻¹ x ≠ x := fun h4 => hx (by simpa using (Equiv.Perm.inv_eq_iff_eq.1 h4).symm)
  rw [Pi.single_eq_of_ne h3] at h2
  exact zero_ne_one h2

theorem card_le_card_of_heisenberg_perm {Γ Λ ι : Type*} [Group Γ] [Finite Λ] [Finite ι]
    (π : Γ →* Equiv.Perm Λ) (A Z : Subgroup Γ) [Finite A] (hA : IsMulCommutative A)
    (hZA : Z ≤ A) (y : ι → Γ) (hcomm : ∀ i, ∀ a ∈ A, ⁅(y i)⁻¹, a⁆ ∈ Z)
    (hHD : ∀ i j, i ≠ j → ∀ u ∈ Z, ∃ a ∈ A, ⁅(y i)⁻¹, a⁆ = u * ⁅(y j)⁻¹, a⁆)
    (hnt : ∃ z ∈ Z, π z ≠ 1) :
    Nat.card ι ≤ Nat.card Λ := by
  have := Fintype.ofFinite Λ
  obtain ⟨z, hzZ, hz⟩ := hnt
  have hinv : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h := card_le_finrank_of_heisenberg ((permFunHom Λ).comp π) A Z hA hinv hZA y hcomm hHD
    ⟨z, hzZ, permFunHom_ne_one hz⟩
  rwa [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card] at h

def antiInv {Λ : Type*} (σ : Equiv.Perm Λ) : Submodule ℂ (Λ → ℂ) where
  carrier := {f | ∀ x, f (σ x) = - f x}
  add_mem' := fun {f g} hf hg x => by
    simp only [Pi.add_apply, hf x, hg x, neg_add]
  zero_mem' := fun x => by simp
  smul_mem' := fun c f hf x => by
    simp only [Pi.smul_apply, hf x, smul_neg]

theorem mem_antiInv {Λ : Type*} {σ : Equiv.Perm Λ} {f : Λ → ℂ} :
    f ∈ antiInv σ ↔ ∀ x, f (σ x) = - f x := Iff.rfl

theorem permFunHom_mem_antiInv {Λ : Type*} {σ τ : Equiv.Perm Λ} (h : τ * σ = σ * τ) {f : Λ → ℂ}
    (hf : f ∈ antiInv σ) : permFunHom Λ τ f ∈ antiInv σ := by
  intro x
  have h1 : τ⁻¹ * σ = σ * τ⁻¹ := (Commute.inv_left (show Commute τ σ from h)).eq
  have h2 : τ⁻¹ (σ x) = σ (τ⁻¹ x) := by
    have := congrArg (fun p : Equiv.Perm Λ => p x) h1
    simpa using this
  simp only [permFunHom_apply, h2, hf (τ⁻¹ x)]

@[expose] def antiInvRep {Λ G : Type*} [Group G] (σ : Equiv.Perm Λ) (π : G →* Equiv.Perm Λ)
    (h : ∀ g, π g * σ = σ * π g) : G →* Module.End ℂ (antiInv σ) where
  toFun g := (permFunHom Λ (π g)).restrict fun _ hf => permFunHom_mem_antiInv (h g) hf
  map_one' := by
    refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
    simp
  map_mul' g g' := by
    refine LinearMap.ext fun f => Subtype.ext (funext fun x => ?_)
    simp

@[simp]
theorem antiInvRep_apply_coe {Λ G : Type*} [Group G] (σ : Equiv.Perm Λ) (π : G →* Equiv.Perm Λ)
    (h : ∀ g, π g * σ = σ * π g) (g : G) (f : antiInv σ) :
    ((antiInvRep σ π h g f : antiInv σ) : Λ → ℂ) = permFunHom Λ (π g) f := rfl

theorem exists_ne_zero_mem_antiInv {Λ : Type*} {σ : Equiv.Perm Λ} (hσ : σ * σ = 1)
    (hne : σ ≠ 1) : ∃ f ∈ antiInv σ, f ≠ 0 := by
  classical
  have hσσ : ∀ z, σ (σ z) = z := fun z => by simpa using congrArg (fun p : Equiv.Perm Λ => p z) hσ
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    exact hne (Equiv.ext fun z => by simpa using h z)
  refine ⟨fun y => (if y = x then (1 : ℂ) else 0) - (if y = σ x then 1 else 0), ?_, ?_⟩
  · intro y
    have e1 : σ y = x ↔ y = σ x := by
      constructor
      · intro h
        rw [← h, hσσ]
      · intro h
        rw [h, hσσ]
    have e2 : σ y = σ x ↔ y = x := σ.injective.eq_iff
    simp only [e1, e2]
    ring
  · intro h
    have := congrFun h x
    simp [Ne.symm hx] at this

theorem antiInvRep_ne_one {Λ G : Type*} [Group G] {σ : Equiv.Perm Λ} (hσ : σ * σ = 1)
    (hne : σ ≠ 1) (π : G →* Equiv.Perm Λ) (h : ∀ g, π g * σ = σ * π g) {g : G} (hg : π g = σ) :
    antiInvRep σ π h g ≠ 1 := by
  intro hρ
  obtain ⟨f, hf, hf0⟩ := exists_ne_zero_mem_antiInv hσ hne
  have h1 : antiInvRep σ π h g ⟨f, hf⟩ = ⟨f, hf⟩ := by rw [hρ]; rfl
  have h2 : permFunHom Λ σ f = f := by
    have := congrArg Subtype.val h1
    rwa [antiInvRep_apply_coe, hg] at this
  apply hf0
  funext y
  have h3 : f (σ⁻¹ y) = f y := congrFun h2 y
  rw [inv_eq_of_mul_eq_one_right hσ] at h3
  have h5 := hf y
  rw [h3] at h5
  exact self_eq_neg.1 h5

theorem two_mul_finrank_antiInv_le {Λ : Type*} [Finite Λ] (σ : Equiv.Perm Λ) (hσ : σ * σ = 1) :
    2 * Module.finrank ℂ (antiInv σ) ≤ Nat.card Λ := by
  classical
  have hσσ : ∀ z, σ (σ z) = z := fun z => by simpa using congrArg (fun p : Equiv.Perm Λ => p z) hσ
  let e : Λ ≃ Fin (Nat.card Λ) := Finite.equivFin Λ
  let S : Set Λ := {x | σ x ≠ x ∧ e x < e (σ x)}
  have := Fintype.ofFinite S
  let r : antiInv σ →ₗ[ℂ] (S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Subtype.val : S → Λ)).comp (antiInv σ).subtype
  have hr : Function.Injective r := by
    refine (injective_iff_map_eq_zero r).2 fun f hf => ?_
    have hf0 : ∀ x : Λ, x ∈ S → (f : Λ → ℂ) x = 0 := fun x hx => congrFun hf ⟨x, hx⟩
    have hfσ : ∀ x, (f : Λ → ℂ) (σ x) = - (f : Λ → ℂ) x := f.2
    refine Subtype.ext (funext fun x => ?_)
    show (f : Λ → ℂ) x = 0
    by_cases hx : σ x = x
    · have h1 := hfσ x
      rw [hx] at h1
      exact self_eq_neg.1 h1
    · rcases lt_or_gt_of_ne (fun h => hx (e.injective h).symm) with h | h
      · exact hf0 x ⟨hx, h⟩
      · have h1 : σ x ∈ S := ⟨by rw [hσσ]; exact Ne.symm hx, by rw [hσσ]; exact h⟩
        have h2 := hfσ x
        rw [hf0 _ h1] at h2
        exact neg_eq_zero.1 h2.symm
  have h1 : Module.finrank ℂ (antiInv σ) ≤ Fintype.card S := by
    have := LinearMap.finrank_le_finrank_of_injective hr
    rwa [Module.finrank_fintype_fun_eq_card] at this
  have h2 : Nat.card S + Nat.card S ≤ Nat.card Λ := by
    rw [← Nat.card_sum]
    refine Nat.card_le_card_of_injective (Sum.elim Subtype.val fun x => σ x.1) ?_
    rintro (⟨x, hx⟩ | ⟨x, hx⟩) (⟨x', hx'⟩ | ⟨x', hx'⟩) h
    · simp only [Sum.elim_inl] at h
      exact congrArg Sum.inl (Subtype.ext h)
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      exfalso
      have h3 : σ x = x' := by rw [h, hσσ]
      have h4 := hx.2
      have h5 := hx'.2
      rw [h3] at h4
      rw [← h] at h5
      exact lt_asymm h4 h5
    · simp only [Sum.elim_inl, Sum.elim_inr] at h
      exfalso
      have h3 : σ x' = x := by rw [← h, hσσ]
      have h4 := hx.2
      have h5 := hx'.2
      rw [h3] at h5
      rw [h] at h4
      exact lt_asymm h4 h5
    · simp only [Sum.elim_inr] at h
      exact congrArg Sum.inr (Subtype.ext (σ.injective h))
  rw [← Nat.card_eq_fintype_card] at h1
  omega

theorem two_mul_card_le_card_of_heisenberg_perm {Γ Λ ι : Type*} [Group Γ] [Finite Λ] [Finite ι]
    (π : Γ →* Equiv.Perm Λ) (A Z : Subgroup Γ) [Finite A] (hA : IsMulCommutative A)
    (hZA : Z ≤ A) (y : ι → Γ) (hcomm : ∀ i, ∀ a ∈ A, ⁅(y i)⁻¹, a⁆ ∈ Z)
    (hHD : ∀ i j, i ≠ j → ∀ u ∈ Z, ∃ a ∈ A, ⁅(y i)⁻¹, a⁆ = u * ⁅(y j)⁻¹, a⁆)
    {z₀ : Γ} (hz₀ : z₀ ∈ Z) (hz₀sq : z₀ * z₀ = 1) (hπz₀ : π z₀ ≠ 1)
    (hyz : ∀ i, y i * z₀ = z₀ * y i) :
    2 * Nat.card ι ≤ Nat.card Λ := by
  classical
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.mp hA ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨C, hmemC⟩ : ∃ C : Subgroup Γ, ∀ g, g ∈ C ↔ g * z₀ = z₀ * g :=
    ⟨Subgroup.centralizer {z₀}, fun g => Subgroup.mem_centralizer_singleton_iff⟩
  have hAC : A ≤ C := fun a ha => (hmemC a).2 (hAcomm a ha z₀ (hZA hz₀))
  have hyC : ∀ i, y i ∈ C := fun i => (hmemC _).2 (hyz i)
  have hz₀C : z₀ ∈ C := (hmemC z₀).2 rfl
  have hσ : π z₀ * π z₀ = 1 := by rw [← map_mul, hz₀sq, map_one]
  let π' : C →* Equiv.Perm Λ := π.comp C.subtype
  have hπ' : ∀ g : C, π' g * π z₀ = π z₀ * π' g := fun g => by
    show π (g : Γ) * π z₀ = π z₀ * π (g : Γ)
    rw [← map_mul, ← map_mul, (hmemC g).1 g.2]
  let ρ := antiInvRep (π z₀) π' hπ'
  let A' : Subgroup C := A.subgroupOf C
  let Z' : Subgroup C := Z.subgroupOf C
  let y' : ι → C := fun i => ⟨y i, hyC i⟩
  have hcoe : ∀ g h : C, ((⁅g, h⁆ : C) : Γ) = ⁅(g : Γ), (h : Γ)⁆ := fun g h => by
    simp [commutatorElement_def]
  have : Finite A' := Finite.of_equiv A (Subgroup.subgroupOfEquivOfLe hAC).symm.toEquiv
  have hA' : IsMulCommutative A' := isMulCommutative_iff.2 fun a b =>
    Subtype.ext <| Subtype.ext <|
      hAcomm _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)
  have hinv : (Nat.card A' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hZA' : Z' ≤ A' := fun g hg =>
    Subgroup.mem_subgroupOf.2 (hZA (Subgroup.mem_subgroupOf.1 hg))
  have hcomm' : ∀ i, ∀ a ∈ A', ⁅(y' i)⁻¹, a⁆ ∈ Z' := fun i a ha => by
    rw [Subgroup.mem_subgroupOf, hcoe]
    exact hcomm i a (Subgroup.mem_subgroupOf.1 ha)
  have hHD' : ∀ i j, i ≠ j → ∀ u ∈ Z', ∃ a ∈ A', ⁅(y' i)⁻¹, a⁆ = u * ⁅(y' j)⁻¹, a⁆ := by
    intro i j hij u hu
    obtain ⟨a, ha, hia⟩ := hHD i j hij u (Subgroup.mem_subgroupOf.1 hu)
    refine ⟨⟨a, hAC ha⟩, Subgroup.mem_subgroupOf.2 ha, Subtype.ext ?_⟩
    rw [hcoe, Subgroup.coe_mul, hcoe]
    exact hia
  have hnt' : ∃ z ∈ Z', ρ z ≠ 1 :=
    ⟨⟨z₀, hz₀C⟩, Subgroup.mem_subgroupOf.2 hz₀, antiInvRep_ne_one hσ hπz₀ π' hπ' rfl⟩
  have key := card_le_finrank_of_heisenberg ρ A' Z' hA' hinv hZA' y' hcomm' hHD' hnt'
  have := two_mul_finrank_antiInv_le (π z₀) hσ
  omega

end CFSG.SignalizerFunctorTheorem.NonLocal

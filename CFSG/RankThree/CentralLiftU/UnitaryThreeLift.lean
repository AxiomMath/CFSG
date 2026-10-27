module

public import CFSG.RankThree.CentralLiftU.UnitaryThreeSplit
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration

public section

namespace CFSG.RankThree.CentralLiftU

open CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.CentralLift
open scoped Matrix

universe u v w

section Package

variable {H : Type u} [Group H] {E : Type v} {G : Type*} [Group E] [Group G]

theorem lifting_package [Finite H] [Group.IsPerfect H] [Finite E] {p : ℕ}
    (hsplit : ∀ (R : Type (max u v)) [Group R] [Finite R] (ρ : R →* H),
      Function.Surjective ρ → ρ.ker ≤ Subgroup.center R → IsPGroup p ρ.ker →
        ∃ s : H →* R, ∀ x, ρ (s x) = x)
    (π : E →* G) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup p π.ker) (α : H →* G) :
    (∃! αh : H →* E, π.comp αh = α) ∧
    ∀ αh : H →* E, π.comp αh = α →
      (Function.Injective α → Function.Injective αh) ∧
      (∀ (e : E) (β : H →* E),
        π.comp β = (MulAut.conj (π e)).toMonoidHom.comp α ↔
          β = (MulAut.conj e).toMonoidHom.comp αh) ∧
      ∀ g : G, (∀ x, g * α x = α x * g) → ∀ e : E, π e = g → ∀ x, e * αh x = αh x * e := by
  have hlift : ∀ β : H →* G, (∃ βh : H →* E, π.comp βh = β) ∧
      ∀ β₁ β₂ : H →* E, π.comp β₁ = β → π.comp β₂ = β → β₁ = β₂ := fun β =>
    ⟨exists_lift_of_forall_section_prime hsplit hπ hC hCp β,
      fun β₁ β₂ h₁ h₂ => eq_of_comp_eq_of_isPerfect hC (h₁.trans h₂.symm)⟩
  obtain ⟨⟨αh, hαh⟩, -⟩ := hlift α
  refine ⟨⟨αh, hαh, fun β hβ => (hlift α).2 β αh hβ hαh⟩, fun αh' hαh' => ?_⟩
  have hconj : ∀ e : E, π.comp ((MulAut.conj e).toMonoidHom.comp αh') =
      (MulAut.conj (π e)).toMonoidHom.comp α := by
    intro e
    ext x
    change π (e * αh' x * e⁻¹) = π e * α x * (π e)⁻¹
    rw [map_mul, map_mul, map_inv, ← DFunLike.congr_fun hαh' x]
    rfl
  refine ⟨fun hα x y hxy => hα ?_, fun e β => ⟨fun hβ => ?_, fun hβ => ?_⟩,
    fun g hg e he x => ?_⟩
  · rw [← DFunLike.congr_fun hαh' x, ← DFunLike.congr_fun hαh' y]
    exact congrArg π hxy
  · exact (hlift _).2 β _ hβ (hconj e)
  · rw [hβ]
    exact hconj e
  · have hα : (MulAut.conj (π e)).toMonoidHom.comp α = α := by
      ext y
      change π e * α y * (π e)⁻¹ = α y
      rw [he, hg y, mul_inv_cancel_right]
    have h := (hlift α).2 _ αh' ((hconj e).trans hα) hαh'
    have hx := DFunLike.congr_fun h x
    change e * αh' x * e⁻¹ = αh' x at hx
    calc e * αh' x = e * αh' x * e⁻¹ * e := by group
      _ = αh' x * e := by rw [hx]

theorem forall_section_of_mulEquiv {H' : Type*} [Group H'] (e : H ≃* H') {p : ℕ}
    {R : Type w} [Group R] [Finite R]
    (hsplit : ∀ ρ : R →* H', Function.Surjective ρ → ρ.ker ≤ Subgroup.center R →
      IsPGroup p ρ.ker → ∃ s : H' →* R, ∀ x, ρ (s x) = x)
    (ρ : R →* H) (hρ : Function.Surjective ρ) (hcen : ρ.ker ≤ Subgroup.center R)
    (hp : IsPGroup p ρ.ker) : ∃ s : H →* R, ∀ x, ρ (s x) = x := by
  have hker : (e.toMonoidHom.comp ρ).ker = ρ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective]
  obtain ⟨s, hs⟩ := hsplit (e.toMonoidHom.comp ρ) (e.surjective.comp hρ) (hker ▸ hcen)
    (hker ▸ hp)
  exact ⟨s.comp e.toMonoidHom, fun x => e.injective (hs (e x))⟩

end Package

section Gram

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem gramSU_eq_SUgram {n : ℕ} (G₀ : Matrix (Fin n) (Fin n) K) :
    gramSU h G₀ = SUgram h.bar G₀ :=
  Subgroup.ext fun _ => And.comm

theorem nonempty_gramSU_mulEquiv_SU {n : ℕ} {G₀ : Matrix (Fin n) (Fin n) K}
    (hG : (G₀.map h.bar)ᵀ = G₀) (hdet : G₀.det ≠ 0) :
    Nonempty (gramSU h G₀ ≃*
      @SU K _ (@unitaryInvolution K _ h.finite ℓ f ⟨h.prime⟩ h.charP) n) := by
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.charP
  have hG' : ∀ i j, h.bar (G₀ j i) = G₀ i j := fun i j => congrFun (congrFun hG i) j
  obtain ⟨e⟩ := nonempty_SUgram_mulEquiv h hG' hdet
  exact ⟨(MulEquiv.subgroupCongr (gramSU_eq_SUgram h G₀)).trans e⟩

theorem gramSU_three_forall_section (hℓ : ℓ ≠ 2) {G₀ : Matrix (Fin 3) (Fin 3) K}
    (hG : (G₀.map h.bar)ᵀ = G₀) (hdet : G₀.det ≠ 0) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (R : Type w) [Group R] [Finite R] (ρ : R →* gramSU h G₀) (hρ : Function.Surjective ρ)
    (hcen : ρ.ker ≤ Subgroup.center R) (hpk : IsPGroup p ρ.ker) :
    ∃ s : gramSU h G₀ →* R, ∀ x, ρ (s x) = x := by
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.charP
  obtain ⟨e⟩ := nonempty_gramSU_mulEquiv_SU h hG hdet
  exact forall_section_of_mulEquiv e (fun ρ' hρ' hcen' hp' =>
    exists_section_SU_three_large (CFSG.LieType.Steinberg.card_eq_sq_of_unitaryFieldData h) hℓ
      hp hp3 hρ' hcen' hp') ρ hρ hcen hpk

theorem finite_isPerfect_gramSU_three (hℓ : ℓ ≠ 2) {G₀ : Matrix (Fin 3) (Fin 3) K}
    (hG : (G₀.map h.bar)ᵀ = G₀) (hdet : G₀.det ≠ 0) :
    Finite (gramSU h G₀) ∧ Group.IsPerfect (gramSU h G₀) := by
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.charP
  obtain ⟨e⟩ := nonempty_gramSU_mulEquiv_SU h hG hdet
  have : Group.IsPerfect (SU (unitaryInvolution K ℓ f) 3) :=
    isPerfect_SU_three (CFSG.LieType.Steinberg.card_eq_sq_of_unitaryFieldData h) hℓ
  exact ⟨Finite.of_equiv _ e.symm.toEquiv,
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

theorem odd_unitary_three_central_large_prime_homomorphism_lifting (hℓ : Odd ℓ)
    {G₀ : Matrix (Fin 3) (Fin 3) K} (hG : (G₀.map h.bar)ᵀ = G₀) (hdet : G₀.det ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {E G : Type*} [Group E] [Group G] [Finite E] [Finite G]
    (π : E →* G) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup p π.ker) (α : gramSU h G₀ →* G) :
    (∃! αh : gramSU h G₀ →* E, π.comp αh = α) ∧
    ∀ αh : gramSU h G₀ →* E, π.comp αh = α →
      (Function.Injective α → Function.Injective αh) ∧
      (∀ (e : E) (β : gramSU h G₀ →* E),
        π.comp β = (MulAut.conj (π e)).toMonoidHom.comp α ↔
          β = (MulAut.conj e).toMonoidHom.comp αh) ∧
      ∀ g : G, (∀ x, g * α x = α x * g) → ∀ e : E, π e = g → ∀ x, e * αh x = αh x * e := by
  have hℓ2 : ℓ ≠ 2 := fun h2 => by rw [h2] at hℓ; exact absurd hℓ (by decide)
  obtain ⟨hfin, hperf⟩ := finite_isPerfect_gramSU_three h hℓ2 hG hdet
  exact lifting_package (fun R _ _ ρ hρ hcen hpk =>
    gramSU_three_forall_section h hℓ2 hG hdet hp hp3 R ρ hρ hcen hpk) π hπ hC hCp α

end Gram

section Abstract

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
  {V : Type*} [AddCommGroup V] [Module K V]

theorem nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid {n : ℕ} {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (e : Module.Basis (Fin n) K V) (he : ∀ i j, B (e i) (e j) = if i = j then 1 else 0) :
    Nonempty (sesqSpecialUnitaryGroup B ≃* SUid h.barEquiv n) := by
  let Ψ := Matrix.GeneralLinearGroup.toLin' e
  have hEq : (SUid h.barEquiv n).map Ψ.toMonoidHom = sesqSpecialUnitaryGroup B := by
    ext g
    constructor
    · rintro ⟨M, hM, rfl⟩
      exact (toLin'_mem_sesqSpecialUnitaryGroup_iff h e he M).2 hM
    · intro hg
      refine ⟨Ψ.symm g, (toLin'_mem_sesqSpecialUnitaryGroup_iff h e he _).1 ?_, ?_⟩
      · change Ψ (Ψ.symm g) ∈ _
        rwa [MulEquiv.apply_symm_apply]
      · exact Ψ.apply_symm_apply g
  exact ⟨((Ψ.subgroupMap (SUid h.barEquiv n)).trans (MulEquiv.subgroupCongr hEq)).symm⟩

theorem barEquiv_eq_unitaryInvolution [Finite K] [Fact ℓ.Prime] [CharP K ℓ] :
    h.barEquiv = unitaryInvolution K ℓ f :=
  RingEquiv.ext fun c => (h.bar_apply c).trans (unitaryInvolution_apply K ℓ f c).symm

theorem odd_unitary_three_central_large_prime_homomorphism_lifting' (hℓ : Odd ℓ)
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : Module.finrank K V = 3) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E G : Type*} [Group E]
    [Group G] [Finite E] [Finite G] (π : E →* G) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup p π.ker)
    (α : sesqSpecialUnitaryGroup B →* G) :
    (∃! αh : sesqSpecialUnitaryGroup B →* E, π.comp αh = α) ∧
    ∀ αh : sesqSpecialUnitaryGroup B →* E, π.comp αh = α →
      (Function.Injective α → Function.Injective αh) ∧
      (∀ (e : E) (β : sesqSpecialUnitaryGroup B →* E),
        π.comp β = (MulAut.conj (π e)).toMonoidHom.comp α ↔
          β = (MulAut.conj e).toMonoidHom.comp αh) ∧
      ∀ g : G, (∀ x, g * α x = α x * g) → ∀ e : E, π e = g → ∀ x, e * αh x = αh x * e := by
  have hℓ2 : ℓ ≠ 2 := fun h2 => by rw [h2] at hℓ; exact absurd hℓ (by decide)
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.charP
  have : FiniteDimensional K V := FiniteDimensional.of_finrank_pos (by omega)
  have hK := CFSG.LieType.Steinberg.card_eq_sq_of_unitaryFieldData h
  obtain ⟨b', hb'⟩ : ∃ b' : Module.Basis (Fin 3) K V,
      ∀ i j, B (b' i) (b' j) = if i = j then 1 else 0 := by
    obtain ⟨c, hc⟩ := h.exists_orthonormal_basis hB hBl
    exact ⟨c.reindex (finCongr hV), fun i j => by
      rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hc]
      simp⟩
  obtain ⟨e₁⟩ := nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid h b' hb'
  have hS : SUid h.barEquiv 3 = SUid (unitaryInvolution K ℓ f) 3 := by
    rw [barEquiv_eq_unitaryInvolution h]
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 3
  let e : sesqSpecialUnitaryGroup B ≃* SU (unitaryInvolution K ℓ f) 3 :=
    (e₁.trans (MulEquiv.subgroupCongr hS)).trans (conjEquiv P hP).symm
  have : Group.IsPerfect (SU (unitaryInvolution K ℓ f) 3) := isPerfect_SU_three hK hℓ2
  have : Finite (sesqSpecialUnitaryGroup B) := Finite.of_equiv _ e.symm.toEquiv
  have : Group.IsPerfect (sesqSpecialUnitaryGroup B) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact lifting_package (fun R _ _ ρ hρ hcen hpk => forall_section_of_mulEquiv e
    (fun ρ' hρ' hcen' hp' => exists_section_SU_three_large hK hℓ2 hp hp3 hρ' hcen' hp')
    ρ hρ hcen hpk) π hπ hC hCp α

end Abstract

section Large

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
  {G₀ : Matrix (Fin 3) (Fin 3) K} {E G : Type*} [Group E] [Group G] [Finite E] {π : E →* G}

noncomputable abbrev su3Lift (π : E →* G) (α : gramSU h G₀ →* G) : gramSU h G₀ →* E :=
  perfectLift π α

variable (hℓ : ℓ ≠ 2) (hG : (G₀.map h.bar)ᵀ = G₀) (hdet : G₀.det ≠ 0)
  (hπ : IsLargeCentralExt π)
include hℓ hG hdet hπ

theorem existsUnique_su3Lift_large (α : gramSU h G₀ →* G) :
    ∃! β : gramSU h G₀ →* E, π.comp β = α := by
  have : Finite G := Finite.of_surjective π hπ.surj
  obtain ⟨p, hp, hp3, hpk⟩ := hπ.large
  have hℓodd : Odd ℓ := h.prime.odd_of_ne_two hℓ
  exact (odd_unitary_three_central_large_prime_homomorphism_lifting h hℓodd hG hdet hp hp3 π
    hπ.surj hπ.cen hpk α).1

theorem comp_su3Lift_large (α : gramSU h G₀ →* G) : π.comp (su3Lift h π α) = α :=
  comp_perfectLift_of_exists (existsUnique_su3Lift_large h hℓ hG hdet hπ α).exists

theorem map_su3Lift_large (α : gramSU h G₀ →* G) (x : gramSU h G₀) :
    π (su3Lift h π α x) = α x :=
  DFunLike.congr_fun (comp_su3Lift_large h hℓ hG hdet hπ α) x

theorem eq_su3Lift_large {α : gramSU h G₀ →* G} {β : gramSU h G₀ →* E}
    (hβ : π.comp β = α) : β = su3Lift h π α :=
  (existsUnique_su3Lift_large h hℓ hG hdet hπ α).unique hβ (comp_su3Lift_large h hℓ hG hdet hπ α)

theorem su3Lift_injective_large {α : gramSU h G₀ →* G} (hα : Function.Injective α) :
    Function.Injective (su3Lift h π α) := by
  intro x y hxy
  apply hα
  rw [← map_su3Lift_large h hℓ hG hdet hπ α, ← map_su3Lift_large h hℓ hG hdet hπ α, hxy]

theorem conj_su3Lift_large (α : gramSU h G₀ →* G) (e : E) :
    (MulAut.conj e).toMonoidHom.comp (su3Lift h π α) =
      su3Lift h π ((MulAut.conj (π e)).toMonoidHom.comp α) := by
  apply eq_su3Lift_large h hℓ hG hdet hπ
  ext x
  change π (e * su3Lift h π α x * e⁻¹) = π e * α x * (π e)⁻¹
  rw [map_mul, map_mul, map_inv, map_su3Lift_large h hℓ hG hdet hπ α x]

theorem conj_su3Lift_apply_large (α : gramSU h G₀ →* G) (e : E) (x : gramSU h G₀) :
    e * su3Lift h π α x * e⁻¹ = su3Lift h π ((MulAut.conj (π e)).toMonoidHom.comp α) x :=
  DFunLike.congr_fun (conj_su3Lift_large h hℓ hG hdet hπ α e) x

end Large

end CFSG.RankThree.CentralLiftU

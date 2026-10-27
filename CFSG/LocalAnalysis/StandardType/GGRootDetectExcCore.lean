module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectCore
public import CFSG.LieType.Chevalley.RootCharacterConjugation

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal

namespace RootDetectExc

section Field

variable {K : Type*} [Field K]

theorem ringEquiv_cases_of_cubic (σ : K ≃+* K) {d e₁ e₂ e₃ : K} (hd : d ≠ 0)
    (h : ∀ t, d * σ t = e₁ * t + e₂ * t ^ 2 + e₃ * t ^ 3) :
    (∀ t, σ t = t) ∨ (∀ t, σ t = t ^ 2) ∨ (∀ t, σ t = t ^ 3) := by
  classical
  by_contra hne
  simp only [not_or, not_forall] at hne
  obtain ⟨⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩, ⟨t₃, ht₃⟩⟩ := hne
  have hli := linearIndependent_monoidHom K K
  let χ : K →* K := σ.toMonoidHom
  have h1 : χ ≠ MonoidHom.id K := fun e => ht₁ (DFunLike.congr_fun e t₁)
  have h2 : χ ≠ powMonoidHom 2 := fun e => ht₂ (DFunLike.congr_fun e t₂)
  have h3 : χ ≠ powMonoidHom 3 := fun e => ht₃ (DFunLike.congr_fun e t₃)
  let l : (K →* K) →₀ K := Finsupp.single χ d - Finsupp.single (MonoidHom.id K) e₁ -
    Finsupp.single (powMonoidHom 2) e₂ - Finsupp.single (powMonoidHom 3) e₃
  have hl : Finsupp.linearCombination K (fun f : K →* K => (f : K → K)) l = 0 := by
    simp only [l, map_sub, Finsupp.linearCombination_single]
    funext t
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, χ,
      MonoidHom.id_apply, powMonoidHom_apply]
    change d * σ t - e₁ * t - e₂ * t ^ 2 - e₃ * t ^ 3 = 0
    rw [h t]
    ring
  have h0 := linearIndependent_iff.mp hli l hl
  have hχ := congrArg (fun m : (K →* K) →₀ K => m χ) h0
  simp only [l, Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne h1, Finsupp.single_eq_of_ne h2, Finsupp.single_eq_of_ne h3,
    Finsupp.coe_zero, Pi.zero_apply, sub_zero] at hχ
  exact hd hχ

theorem eq_one_of_forall_eq_cube [CharP K 2] (σ : K ≃+* K) (h : ∀ t, σ t = t ^ 3) : σ = 1 := by
  refine RingEquiv.ext fun t => ?_
  change σ t = t
  have h1 := h (t + 1)
  rw [map_add, map_one, h t] at h1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : t * (t + 1) = 0 := by linear_combination (-1 : K) * h1 - (t ^ 2 + t) * h2
  rcases mul_eq_zero.mp h3 with h0 | h0
  · rw [h0, map_zero]
  · have ht : t = 1 := by
      have : t = -1 := eq_neg_of_add_eq_zero_left h0
      rw [this, CharTwo.neg_eq]
    rw [ht, map_one]

theorem eq_one_of_eq_inv_of_odd {G : Type*} [Group G] {σ : G} {p : ℕ} (hp : Odd p)
    (hσp : σ ^ p = 1) (h : σ = σ⁻¹) : σ = 1 := by
  have h2 : σ ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h]
    exact mul_inv_cancel σ
  obtain ⟨m, rfl⟩ := hp
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hσp
  exact hσp

end Field

section Adjoint


variable {τ : Tag} (F : RootOperatorFamily τ) {K : Type} [Field K]

theorem exists_cubic_of_conj_elt (α : Root τ) (N : (Module.End K (RootModule τ K))ˣ)
    (σ : K ≃+* K)
    (h : ∀ t, ((N⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) *
      F.elt K α t * (N : Module.End K (RootModule τ K)) = F.elt K α (σ t)) :
    ∃ d : K, d ≠ 0 ∧ ∃ e₁ e₂ e₃ : K, ∀ t, d * σ t = e₁ * t + e₂ * t ^ 2 + e₃ * t ^ 3 := by
  obtain ⟨a, b, hab⟩ := RootOperatorFamily'.exists_D_one_apply_ne_zero F (R := K) α
  have hshift : labelWt τ a = labelWt τ b + α.1 := by
    have := F.mapsLabelWt_D (R := K) α le_rfl a b hab
    rwa [one_nsmul] at this
  have hba : b ≠ a := by
    rintro rfl
    exact α.2.ne_zero (by simpa using hshift)
  set M : ℕ → K := fun k =>
    (((N⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) *
      F.D K α k * (N : Module.End K (RootModule τ K))) (Finsupp.single b 1) a with hM
  have hM0 : M 0 = 0 := by
    simp only [hM, F.D_zero, mul_one, Units.inv_mul, Module.End.one_apply]
    simp [hba]
  refine ⟨F.D K α 1 (Finsupp.single b 1) a, hab, M 1, M 2, M 3, fun t => ?_⟩
  have e := congrArg (fun A : Module.End K (RootModule τ K) => A (Finsupp.single b 1) a) (h t)
  rw [RootOperatorFamily'.elt_apply_of_shift F α (σ t) hshift] at e
  rw [mul_comm, ← e, RootOperatorFamily.elt, Finset.mul_sum, Finset.sum_mul,
    LinearMap.sum_apply, Finsupp.finsetSum_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, mul_smul_comm, smul_mul_assoc,
    LinearMap.smul_apply, Finsupp.smul_apply, smul_eq_mul]
  have h0 := hM0
  simp only [hM] at h0
  rw [h0]
  simp only [hM]
  ring

theorem ringEquiv_eq_one_of_conj_elt [CharP K 2] (α : Root τ)
    {N : (Module.End K (RootModule τ K))ˣ} {σ : K ≃+* K} {p : ℕ} (hp : Odd p)
    (hσp : σ ^ p = 1)
    (h : ∀ t, ((N⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) *
      F.elt K α t * (N : Module.End K (RootModule τ K)) = F.elt K α (σ t)) : σ = 1 := by
  have hcases : ∀ (M : (Module.End K (RootModule τ K))ˣ) (ρ : K ≃+* K),
      (∀ t, ((M⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) *
        F.elt K α t * (M : Module.End K (RootModule τ K)) = F.elt K α (ρ t)) →
      ρ = 1 ∨ ∀ t, ρ t = t ^ 2 := by
    intro M ρ hM
    obtain ⟨d, hd, e₁, e₂, e₃, he⟩ := exists_cubic_of_conj_elt F α M ρ hM
    rcases ringEquiv_cases_of_cubic ρ hd he with h1 | h2 | h3
    · exact Or.inl (RingEquiv.ext h1)
    · exact Or.inr h2
    · exact Or.inl (eq_one_of_forall_eq_cube ρ h3)
  have hinv : ∀ t, (((N⁻¹)⁻¹ : (Module.End K (RootModule τ K))ˣ) :
      Module.End K (RootModule τ K)) * F.elt K α t *
        ((N⁻¹ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) =
      F.elt K α (σ⁻¹ t) := by
    intro t
    have h1 := h (σ⁻¹ t)
    have h2 : σ (σ⁻¹ t) = t := σ.apply_symm_apply t
    rw [h2] at h1
    rw [inv_inv, ← h1]
    simp only [← mul_assoc, Units.mul_inv, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  rcases hcases N σ h with h1 | h2
  · exact h1
  · rcases hcases N⁻¹ σ⁻¹ hinv with h3 | h4
    · exact inv_eq_one.mp h3
    · exact eq_one_of_eq_inv_of_odd hp hσp (RingEquiv.ext fun t => by rw [h2 t, h4 t])

theorem units_map_entrywiseHom_eltUnit (σ : K ≃+* K) (α : Root τ) (t : K) :
    Units.map (entrywiseHom σ.toRingHom) (F.eltUnit K α t) = F.eltUnit K α (σ t) := by
  obtain ⟨γ, hγ⟩ := α
  have hs := F.pinnedFamilySign_mul_self K γ
  have e1 : ∀ s : K, F.eltUnit K ⟨γ, hγ⟩ s =
      pinnedX τ K γ ((F.pinnedFamilySign γ : K) * s) := by
    intro s
    rw [F.pinnedX_eq_eltUnit K hγ, ← mul_assoc, hs, one_mul]
  refine Units.ext ?_
  rw [Units.coe_map, e1 t, e1 (σ t)]
  change entrywise σ.toRingHom (pinnedX τ K γ _ : Module.End K (RootModule τ K)) = _
  rw [entrywise_pinnedX, map_mul, map_intCast]
  rfl

theorem entrywise_ringHomId (A : Module.End K (RootModule τ K)) :
    entrywise (RingHom.id K) A = A := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single]
  exact Finsupp.mapRange_id _

end Adjoint

section Isogeny


variable {τ : Tag} {K : Type} [Field K]

@[expose] def AdjFieldForm (τ : Tag) (K : Type) [Field K] (p : ℕ) : Prop :=
  ∀ β : MulAut (adjointGroup τ K), β ^ p = 1 →
    ∃ (g : adjointGroup τ K) (σ : K ≃+* K), σ ^ p = 1 ∧ ∀ h : adjointGroup τ K,
      (β h : ModGL τ K) = (g : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
        (g : ModGL τ K)⁻¹

theorem ggPsiInnerDiag_of_isogeny [Finite K] [CharP K 2] (F : RootOperatorFamily τ)
    {S : Type*} [Group S] [Finite S] (Δ : UniversalRootDatum S)
    (hperf : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤)
    (hZ : Subgroup.center (adjointGroup τ K) = ⊥)
    {π : S →* adjointGroup τ K} (hπ : Function.Surjective π)
    (hπker : π.ker ≤ Subgroup.center S) {p : ℕ} (hp : Odd p) (hform : AdjFieldForm τ K p)
    {G : Type*} [Group G] {ψ : S →* G} (hker : ψ.ker ≤ Subgroup.center S) {c : G}
    (hc : c ∈ Subgroup.normalizer (ψ.range : Set G))
    (hcp : c ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) {γ : Fin Δ.rank → ℤ}
    {α : Root τ} (hroot : ∀ t : K, ∃ z ∈ Δ.rootGroup γ, π z = F.eltElement α t)
    {u : S} (hT : GGTorusOnRoot Δ ψ c γ u) :
    GGPsiInnerDiag Δ ψ c := by
  classical
  obtain ⟨α', hα'⟩ := RootDetect.exists_quotAut (N := Subgroup.center S) rfl hperf hker hc
  have hα'p : α' ^ p = 1 := RootDetect.quotAut_pow_eq_one le_rfl hker hc hα' hcp
  have hkerπ : π.ker = Subgroup.center S := by
    refine le_antisymm hπker fun z hz => ?_
    rw [MonoidHom.mem_ker]
    have hzc : π z ∈ Subgroup.center (adjointGroup τ K) := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨y, rfl⟩ := hπ x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hZ] at hzc
    exact hzc
  let e : S ⧸ Subgroup.center S ≃* adjointGroup τ K :=
    (QuotientGroup.quotientMulEquivOfEq hkerπ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have he : ∀ y : S, e (y : S ⧸ Subgroup.center S) = π y := fun y => rfl
  let β : MulAut (adjointGroup τ K) := (e.symm.trans α').trans e
  have hβ : ∀ x, β (e x) = e (α' x) := fun x => by
    change e (α' (e.symm (e x))) = e (α' x)
    rw [MulEquiv.symm_apply_apply]
  have hβpow : ∀ k : ℕ, ∀ x, (β ^ k) (e x) = e ((α' ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih, hβ, pow_succ', MulAut.mul_apply]
  have hβp : β ^ p = 1 := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [hβpow, hα'p]
    rfl
  obtain ⟨g, σ, hσp, hgσ⟩ := hform β hβp
  obtain ⟨W, hW⟩ := RootDetect.exists_conj_of_torusOnRoot Δ hT
  have hconj : ∀ t : K, β (π u * F.eltElement α t * (π u)⁻¹) =
      π W * F.eltElement α t * (π W)⁻¹ := by
    intro t
    obtain ⟨z, hz, hπz⟩ := hroot t
    have h2 := congrArg e (hα' _ _ (hW z hz))
    rw [← hβ, he, he] at h2
    simpa only [map_mul, map_inv, hπz] using h2
  obtain ⟨σu, hσu⟩ : ∃ x : ModGL τ K,
      x = Units.map (entrywiseHom σ.toRingHom) (π u : ModGL τ K) := ⟨_, rfl⟩
  obtain ⟨wW, hwW⟩ : ∃ x : ModGL τ K, x = ((π W : adjointGroup τ K) : ModGL τ K) := ⟨_, rfl⟩
  have hNt : ∀ t : K, (((wW⁻¹ * (g : ModGL τ K) * σu)⁻¹ : (Module.End K (RootModule τ K))ˣ) :
      Module.End K (RootModule τ K)) * F.elt K α t *
        ((wW⁻¹ * (g : ModGL τ K) * σu : (Module.End K (RootModule τ K))ˣ) :
          Module.End K (RootModule τ K)) = F.elt K α (σ t) := by
    intro t
    have h1 : ((β (π u * F.eltElement α t * (π u)⁻¹) : adjointGroup τ K) : ModGL τ K) =
        ((π W * F.eltElement α t * (π W)⁻¹ : adjointGroup τ K) : ModGL τ K) := by
      rw [hconj t]
    rw [hgσ] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
      RootOperatorFamily.coe_eltElement, units_map_entrywiseHom_eltUnit, ← hσu, ← hwW] at h1
    have h1' : (g : ModGL τ K) * σu * F.eltUnit K α (σ t) * σu⁻¹ * (g : ModGL τ K)⁻¹ =
        wW * F.eltUnit K α t * wW⁻¹ := by
      rw [← h1]
      group
    have h3 : (wW⁻¹ * (g : ModGL τ K) * σu) * F.eltUnit K α (σ t) *
        (wW⁻¹ * (g : ModGL τ K) * σu)⁻¹ = F.eltUnit K α t := by
      calc (wW⁻¹ * (g : ModGL τ K) * σu) * F.eltUnit K α (σ t) *
            (wW⁻¹ * (g : ModGL τ K) * σu)⁻¹ =
          wW⁻¹ * ((g : ModGL τ K) * σu * F.eltUnit K α (σ t) * σu⁻¹ * (g : ModGL τ K)⁻¹) *
            wW := by group
        _ = F.eltUnit K α t := by rw [h1']; group
    have h4 : (wW⁻¹ * (g : ModGL τ K) * σu)⁻¹ * F.eltUnit K α t *
        (wW⁻¹ * (g : ModGL τ K) * σu) = F.eltUnit K α (σ t) := by
      rw [← h3]
      group
    exact congrArg Units.val h4
  have hσ : σ = 1 := ringEquiv_eq_one_of_conj_elt F α hp hσp hNt
  have hβg : ∀ h, β h = g * h * g⁻¹ := by
    intro h
    refine Subtype.ext ?_
    rw [hgσ h, hσ]
    refine congrArg (fun x : ModGL τ K => (g : ModGL τ K) * x * (g : ModGL τ K)⁻¹) ?_
    refine Units.ext ?_
    rw [Units.coe_map]
    exact entrywise_ringHomId _
  obtain ⟨a, rfl⟩ := hπ g
  have ha : ∀ y : S, α' (y : S ⧸ Subgroup.center S) =
      ((a * y * a⁻¹ : S) : S ⧸ Subgroup.center S) := by
    intro y
    apply e.injective
    rw [← hβ, he, he, hβg, map_mul, map_mul, map_inv]
  exact RootDetect.ggPsiInnerDiag_of_centralizes Δ
    (RootDetect.centralizes_of_quotAut_conj rfl hperf hc hα' ha)

end Isogeny

end RootDetectExc

end CFSG.StandardType

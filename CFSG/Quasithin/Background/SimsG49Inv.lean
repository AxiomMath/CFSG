module

public import CFSG.Quasithin.Background.SimsG44
import CFSG.Quasithin.Background.SimsG4Core

public section

namespace CFSG.Quasithin.SimsG4

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem G49.exists_commSpace_eq_span {a : V ≃ₗ[F] V} (ha : IsTransv a) :
    ∃ u : V, u ≠ 0 ∧ commSpace a = F ∙ u := by
  obtain ⟨u', hu'0, hu'⟩ := finrank_eq_one_iff'.mp ha.1
  refine ⟨u', fun h => hu'0 (Subtype.ext h), ?_⟩
  ext w
  constructor
  · intro hw
    obtain ⟨c, hc⟩ := hu' ⟨w, hw⟩
    exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
  · intro hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    exact Submodule.smul_mem _ c u'.2

theorem mem_invSet_of_commuting [CharP F 2] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {G₀ : Subgroup (V ≃ₗ[F] V)}
    {a b : V ≃ₗ[F] V} (ha : a ∈ transvSet G₀) (hb : b ∈ transvSet G₀) (hab : a * b = b * a)
    (hc : commSpace a ≠ commSpace b) : a * b ∈ invSet B G₀ := by
  have ha2 : a * a = 1 := transv_mul_self a ha.2
  have hb2 : b * b = 1 := transv_mul_self b hb.2
  refine ⟨(transvGen G₀).mul_mem (Subgroup.subset_closure ha) (Subgroup.subset_closure hb), ?_,
    ?_, a, ha, b, ⟨hb, hab.symm, ?_⟩, rfl⟩
  · intro h1
    have hba : b = a := by
      rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right ha2]
    exact hc (by rw [hba])
  · calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [ha2, hb2, one_mul]
  · intro hR
    obtain ⟨u, hu, hcomm⟩ := G49.exists_commSpace_eq_span ha.2
    obtain ⟨μ, rfl⟩ := (mem_rootGroupHat_iff B halt hnd hu hcomm _).mp hR
    by_cases hμ : μ = 0
    · exact transv_ne_one _ hb.2 (by rw [hμ, symplTransv_coeff_zero])
    · exact hc (by rw [hcomm, commSpace_symplTransv B halt hnd hu hμ])

namespace G49

variable (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)

theorem conj_symplTransv {g : V ≃ₗ[F] V} (hg : g ∈ spGroup B) (w : V) (μ : F) :
    g * symplTransv B halt w μ * g⁻¹ = symplTransv B halt (g w) μ := by
  refine LinearEquiv.ext fun v => ?_
  have h1 : B (g⁻¹ v) w = B v (g w) := by
    have h := hg (g⁻¹ v) w
    rw [mul_inv_apply] at h
    exact h.symm
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, symplTransv_apply, symplTransv_apply, map_add,
    map_smul, mul_inv_apply, h1]

variable (b : Module.Basis (Fin 4) F V)

private theorem ite_mem_subfield (F₀ : Subfield F) (p : Prop) [Decidable p] :
    (if p then (1 : F) else 0) ∈ F₀ := by
  split_ifs
  · exact F₀.one_mem
  · exact F₀.zero_mem

theorem symplTransv_basis_mem_subfieldSpOf (hb : IsSympBasis B b) (F₀ : Subfield F) (i : Fin 4) :
    symplTransv B halt (b i) 1 ∈ subfieldSpOf b F₀ := by
  intro k j
  rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, symplTransv_apply, map_add, map_smul,
    Module.Basis.repr_self, Module.Basis.repr_self, hb, one_mul, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul]
  exact F₀.add_mem (ite_mem_subfield F₀ _) (F₀.mul_mem (ite_mem_subfield F₀ _)
    (ite_mem_subfield F₀ _))

theorem basisEquiv_mem_subfieldSpOf (F₀ : Subfield F) (σ : Equiv.Perm (Fin 4)) :
    b.equiv b σ ∈ subfieldSpOf b F₀ := by
  intro k j
  rw [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  exact ite_mem_subfield F₀ _

theorem basisEquiv_mem_spGroup (hb : IsSympBasis B b) (σ : Equiv.Perm (Fin 4))
    (hσ : ∀ i j : Fin 4, ((σ i).val + (σ j).val = 3 ↔ i.val + j.val = 3)) :
    b.equiv b σ ∈ spGroup B := by
  have h : B.compl₁₂ (b.equiv b σ : V →ₗ[F] V) (b.equiv b σ : V →ₗ[F] V) = B := by
    refine LinearMap.BilinForm.ext_basis b fun i j => ?_
    rw [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Module.Basis.equiv_apply, hb, hb]
    simp only [hσ]
  intro x y
  exact LinearMap.congr_fun₂ h x y

variable (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
include halt hnd

theorem exists_symplTransv_basis [CharP F 2] (hb : IsSympBasis B b) (G₀ : Subgroup (V ≃ₗ[F] V))
    (F₀ : Subfield F) (hG : ∀ g : V ≃ₗ[F] V, g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) :
    ∃ t₀ t₁ t₂ t₃ g : V ≃ₗ[F] V, t₀ ∈ G₀ ∧ t₃ ∈ G₀ ∧ g ∈ G₀ ∧
      t₁ = g * t₀ * g⁻¹ ∧ t₂ = g * t₃ * g⁻¹ ∧ t₀ * t₁ ∈ invSet B G₀ ∧
      t₀ * t₁ * (t₃ * t₂) ≠ t₃ * t₂ * (t₀ * t₁) := by
  have htG : ∀ i, symplTransv B halt (b i) 1 ∈ G₀ := fun i =>
    (hG _).mpr ⟨symplTransv_mem_spGroup B halt (b i) 1,
      symplTransv_basis_mem_subfieldSpOf B halt b hb F₀ i⟩
  have htD : ∀ i, symplTransv B halt (b i) 1 ∈ transvSet G₀ := fun i =>
    ⟨htG i, symplTransv_isTransv B halt hnd (b.ne_zero i) one_ne_zero⟩
  set σ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3 with hσdef
  have hσ : ∀ i j : Fin 4, ((σ i).val + (σ j).val = 3 ↔ i.val + j.val = 3) := by
    rw [hσdef]
    decide
  have hgSp := basisEquiv_mem_spGroup B b hb σ hσ
  have hgG : b.equiv b σ ∈ G₀ := (hG _).mpr ⟨hgSp, basisEquiv_mem_subfieldSpOf b F₀ σ⟩
  have hg0 : b.equiv b σ (b 0) = b 1 := by
    rw [Module.Basis.equiv_apply, hσdef]
    rfl
  have hg3 : b.equiv b σ (b 3) = b 2 := by
    rw [Module.Basis.equiv_apply, hσdef]
    rfl
  have hB : ∀ i j : Fin 4, i.val + j.val ≠ 3 → B (b i) (b j) = 0 := fun i j h => by
    rw [hb, if_neg h]
  have hB' : ∀ i j : Fin 4, i.val + j.val = 3 → B (b i) (b j) = 1 := fun i j h => by
    rw [hb, if_pos h]
  have hcomm : symplTransv B halt (b 0) 1 * symplTransv B halt (b 1) 1 =
      symplTransv B halt (b 1) 1 * symplTransv B halt (b 0) 1 :=
    (SimsG45.transv_commute_iff B halt hnd (b.ne_zero 0) one_ne_zero one_ne_zero
      (symplTransv_apply B halt (b 0) 1) (symplTransv_apply B halt (b 1) 1)).mpr
      (hB 0 1 (by decide))
  have hcen : commSpace (symplTransv B halt (b 0) 1) ≠ commSpace (symplTransv B halt (b 1) 1) := by
    rw [commSpace_symplTransv B halt hnd (b.ne_zero 0) one_ne_zero,
      commSpace_symplTransv B halt hnd (b.ne_zero 1) one_ne_zero]
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      (h ▸ Submodule.mem_span_singleton_self (b 0) : b 0 ∈ F ∙ b 1)
    have h03 := hB' 0 3 (by decide)
    rw [← hc, LinearMap.map_smul₂, hB 1 3 (by decide), smul_zero] at h03
    exact zero_ne_one h03
  refine ⟨symplTransv B halt (b 0) 1, symplTransv B halt (b 1) 1, symplTransv B halt (b 2) 1,
    symplTransv B halt (b 3) 1, b.equiv b σ, htG 0, htG 3, hgG, ?_, ?_,
    mem_invSet_of_commuting B halt hnd (htD 0) (htD 1) hcomm hcen, ?_⟩
  · rw [conj_symplTransv B halt hgSp, hg0]
  · rw [conj_symplTransv B halt hgSp, hg3]
  ·
    intro h
    have h1 := congrArg (fun φ : V ≃ₗ[F] V => φ (b 0)) h
    simp only [LinearEquiv.mul_apply, symplTransv_apply, map_add, LinearMap.add_apply,
      hB 0 2 (by decide), hB' 0 3 (by decide), hB 0 1 (by decide), hB 3 1 (by decide),
      hB 0 0 (by decide), hB' 3 0 (by decide), mul_zero, mul_one, zero_smul, one_smul, add_zero,
      zero_add] at h1
    have h2 : b 0 + b 3 + b 0 = b 0 + b 3 := by rw [add_assoc]; exact h1
    exact b.ne_zero 0 (add_eq_left.mp h2)

end G49

end CFSG.Quasithin.SimsG4

module

public import CFSG.RankThree.GF2n.Smith81.Orth212C5Alg
public import CFSG.RankThree.GF2n.Smith81.Orth212C5Lift
public import CFSG.RankThree.GF2n.Smith81.Orth213Stmts

public section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open CFSG.ClassicalGroups.Orthogonal (eichler)
open scoped commutatorElement

namespace CFSG.RankThree.GF2n.Smith81

namespace OrthC5

variable {G : Type} [Group G] [Finite G]
  {M Q Z B X : Subgroup G} {x : G}

theorem core_E (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    (h4 : Orth212C4CondStatement) (h28 : Smith28OrthStatement)
    (h7 : Orth212C7CondStatement) (hD : Q ⊓ QB X ≠ ⊥)
    (hx : ActsAsTensor Q Z C.M₀ C.φ x !![1, 1; 0, 1] ⇑(LinearEquiv.refl C.K (C.ι → C.K))) :
    (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z := by
  have H := hc.ctx.hyp
  refine sup_eq_of_image hc C hs hx (fun d hd => phi_pi_mem_Rsp hc C hs h4 h28 hx hd) ?_
  have hRsp : ∀ r ∈ OrthCaseI.Rsp C !![1, 1; 0, 1] (LinearEquiv.refl C.K (C.ι → C.K)),
      r.2 = 0 := by
    intro r hr
    obtain ⟨p', hp'⟩ := (OrthCaseI.mem_Rsp_iff C _ _).mp hr
    rw [hp', OrthCaseI.orthTensor_t_apply]
    simp
  let S : AddSubgroup (C.ι → C.K) :=
    { carrier := {v | ∃ d ∈ Q ⊓ QB X, C.φ (C.M₀.π d) = (v, 0)}
      add_mem' := by
        rintro v₁ v₂ ⟨d₁, hd₁, e₁⟩ ⟨d₂, hd₂, e₂⟩
        refine ⟨d₁ * d₂, Subgroup.mul_mem _ hd₁ hd₂, ?_⟩
        rw [C.M₀.π_mul d₁ hd₁.1 d₂ hd₂.1, map_add, e₁, e₂]
        simp
      zero_mem' := ⟨1, Subgroup.one_mem _, by rw [Tim79.QuadModel.pi_one, map_zero]; rfl⟩
      neg_mem' := by
        rintro v ⟨d, hd, e⟩
        refine ⟨d⁻¹, Subgroup.inv_mem _ hd, ?_⟩
        rw [Tim79.QuadModel.pi_inv C.M₀ hd.1, map_neg, e]
        simp }
  have hmemS : ∀ v, v ∈ S ↔ ∃ d ∈ Q ⊓ QB X, C.φ (C.M₀.π d) = (v, 0) := fun v => Iff.rfl
  have hstab : ∀ a w : C.ι → C.K, C.qU a = 0 → polar C.qU a w = 0 → ∀ v ∈ S,
      eichler C.qU a w v ∈ S := by
    intro a w ha hw v hv
    obtain ⟨d, hd, hdv⟩ := (hmemS v).mp hv
    obtain ⟨s, hsL, hsa⟩ := C.hA.eich a w ha hw
    have hsM : s ∈ M := Lgen_le hc.ctx.LB_le_M hsL
    obtain ⟨d', hd', hφd'⟩ := exists_lift hc C hs h7 hD (g' := 1) (o' := eichler C.qU a w)
      hx hsM hsa (fun p => by
        simp only [OrthCaseI.orthTensor_one_apply, OrthCaseI.orthTensor_t_apply,
          LinearEquiv.refl_apply, map_add]) d hd
    refine (hmemS _).mpr ⟨d', hd', ?_⟩
    rw [hφd', hdv, OrthCaseI.orthTensor_one_apply]
    simp
  obtain ⟨v₀, hv₀c, hv₀Q, hv₀X⟩ := h28 G M Q Z B hc X x hs
  have hv₀D : v₀ ∈ Q ⊓ QB X := ⟨hv₀Q, hv₀X⟩
  obtain ⟨g₀, hg₀⟩ := hs.conj
  have hz₀ : g₀⁻¹ * x * g₀ ∈ Z := mem_conjSubgroup.mp (hg₀ ▸ hs.mem)
  have hz₀1 : g₀⁻¹ * x * g₀ ≠ 1 := by
    intro e
    apply hs.ne_one
    calc x = g₀ * (g₀⁻¹ * x * g₀) * g₀⁻¹ := by group
      _ = 1 := by rw [e]; group
  have hz₀x : IsConj (g₀⁻¹ * x * g₀) x := isConj_iff.mpr ⟨g₀, by group⟩
  have hv₀1 : v₀ ≠ 1 := ne_one_of_isConj_Z hs.ne_one hv₀c
  have hv₀Z : v₀ ∉ Z := by
    intro hZ
    have hm : v₀ ∈ Z ⊓ QB X := ⟨hZ, hv₀X⟩
    rw [Z_inf_QB_eq_bot hs (smith_1_12 hs), Subgroup.mem_bot] at hm
    exact hv₀1 hm
  obtain ⟨c₁, c₂, u, hc12, hu0, hqu, hφ⟩ :=
    (C.hF.root _ hz₀ hz₀1 v₀ hv₀Q hv₀Z).mp (hz₀x.trans hv₀c)
  have hr2 : (C.φ (C.M₀.π v₀)).2 = 0 :=
    hRsp _ (phi_pi_mem_Rsp hc C hs h4 h28 hx hv₀D)
  rw [hφ] at hr2
  have hc2 : c₂ = 0 := (smul_eq_zero.mp hr2).resolve_right hu0
  have hc1 : c₁ ≠ 0 := hc12.resolve_right (fun h => h hc2)
  have hsS : c₁ • u ∈ S := (hmemS _).mpr ⟨v₀, hv₀D, by rw [hφ, hc2]; simp⟩
  have hsq : C.qU (c₁ • u) = 0 := by rw [QuadraticMap.map_smul, hqu, smul_zero]
  have hs0 : c₁ • u ≠ 0 := smul_ne_zero hc1 hu0
  have hdim : 4 ≤ Module.finrank C.K (C.ι → C.K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact four_le_card_of_cfg hc C
  have hS : S = ⊤ := eq_top_of_stable C.hF.nondeg hdim hstab hsS hsq hs0
  intro r hr
  have hr2 : r.2 = 0 := hRsp r hr
  have : r.1 ∈ S := by rw [hS]; trivial
  obtain ⟨d, hd, hdr⟩ := (hmemS _).mp this
  exact ⟨d, hd, by rw [hdr]; ext <;> simp [hr2]⟩

theorem core_A (hc : SmithOrthCfg M Q Z B) (C : OrthCtx M Q Z B) (hs : Sit M Q Z X x)
    (h4 : Orth212C4CondStatement) (h28 : Smith28OrthStatement)
    (h7 : Orth212C7CondStatement) (hD : Q ⊓ QB X ≠ ⊥) {u w : C.ι → C.K}
    (hu : C.qU u = 0) (hw : C.qU w = 0) (huw : polar C.qU u w = 0)
    (hind : LinearIndependent C.K ![u, w])
    (hx : ActsAsTensor Q Z C.M₀ C.φ x 1 ⇑(eichler C.qU u w)) :
    (Q ⊓ QB X) ⊔ Z = ⁅Q, Subgroup.zpowers x⁆ ⊔ Z := by
  refine sup_eq_of_image hc C hs hx (fun d hd => phi_pi_mem_Rsp hc C hs h4 h28 hx hd) ?_
  have hspan : ∀ r ∈ OrthCaseI.Rsp C 1 (eichler C.qU u w),
      r.1 ∈ Submodule.span C.K {u, w} ∧ r.2 ∈ Submodule.span C.K {u, w} := by
    intro r hr
    rw [OrthCaseI.Rsp_one, Submodule.mem_prod] at hr
    have h1 : ∀ y ∈ OrthogonalInvolutions.commSpace (eichler C.qU u w),
        y ∈ Submodule.span C.K {u, w} := by
      intro y hy
      obtain ⟨v, rfl⟩ := OrthogonalInvolutions.mem_commSpace.mp hy
      obtain ⟨a, b, hab⟩ :=
        CFSG.ClassicalGroups.Orthogonal.eichler_apply_eq_add (Q := C.qU) u w v
      rw [hab, show v + a • w + b • u - v = a • w + b • u by abel]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    exact ⟨h1 _ hr.1, h1 _ hr.2⟩
  let D' : AddSubgroup ((C.ι → C.K) × (C.ι → C.K)) :=
    { carrier := {p | ∃ d ∈ Q ⊓ QB X, C.φ (C.M₀.π d) = p}
      add_mem' := by
        rintro p₁ p₂ ⟨d₁, hd₁, e₁⟩ ⟨d₂, hd₂, e₂⟩
        refine ⟨d₁ * d₂, Subgroup.mul_mem _ hd₁ hd₂, ?_⟩
        rw [C.M₀.π_mul d₁ hd₁.1 d₂ hd₂.1, map_add, e₁, e₂]
      zero_mem' := ⟨1, Subgroup.one_mem _, by rw [Tim79.QuadModel.pi_one, map_zero]⟩
      neg_mem' := by
        rintro p ⟨d, hd, e⟩
        exact ⟨d⁻¹, Subgroup.inv_mem _ hd, by rw [Tim79.QuadModel.pi_inv C.M₀ hd.1, map_neg, e]⟩ }
  have hmemD : ∀ p, p ∈ D' ↔ ∃ d ∈ Q ⊓ QB X, C.φ (C.M₀.π d) = p := fun p => Iff.rfl
  have hstab : ∀ {g' : Matrix (Fin 2) (Fin 2) C.K} {o' : (C.ι → C.K) ≃ₗ[C.K] (C.ι → C.K)} {s : G},
      s ∈ Lgen M (LB M Q B) → ActsAsTensor Q Z C.M₀ C.φ s g' o' →
      (∀ p, orthTensor 1 (eichler C.qU u w) (orthTensor g' o' p) =
        orthTensor g' o' (orthTensor 1 (eichler C.qU u w) p)) →
      ∀ p ∈ D', orthTensor g' o' p ∈ D' := by
    intro g' o' s hsL hsa hcomm p hp
    obtain ⟨d, hd, rfl⟩ := (hmemD p).mp hp
    obtain ⟨d', hd', hφ⟩ := exists_lift hc C hs h7 hD hx (Lgen_le hc.ctx.LB_le_M hsL) hsa hcomm
      d hd
    exact (hmemD _).mpr ⟨d', hd', hφ⟩
  have hdet1 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) C.K).det = 1 := by
    simp [Matrix.det_fin_two_of]
  have hdet2 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) C.K).det = 1 := by
    simp [Matrix.det_fin_two_of]
  have key := prod_subset_of_stable (q := C.qU) C.hF.nondeg hu hw huw hind (D := D')
    (fun p hp => by
      obtain ⟨d, hd, rfl⟩ := (hmemD p).mp hp
      exact hspan _ (phi_pi_mem_Rsp hc C hs h4 h28 hx hd))
    (by
      obtain ⟨d, hd, hd0⟩ := exists_phi_pi_ne_zero C hs hD
      exact ⟨_, (hmemD _).mpr ⟨d, hd, rfl⟩, hd0⟩)
    (fun p hp => by
      obtain ⟨s, hsL, hsa⟩ := C.hA.sl _ hdet1
      have := hstab (o' := LinearEquiv.refl C.K (C.ι → C.K)) hsL hsa
        (fun p => by
          simp only [OrthCaseI.orthTensor_one_apply, OrthCaseI.orthTensor_t_apply,
            LinearEquiv.refl_apply, map_add]) p hp
      simpa [OrthCaseI.orthTensor_t_apply] using this)
    (fun p hp => by
      obtain ⟨s, hsL, hsa⟩ := C.hA.sl _ hdet2
      have := hstab (o' := LinearEquiv.refl C.K (C.ι → C.K)) hsL hsa
        (fun p => by
          simp [orthTensor, OrthCaseI.orthTensor_one_apply]) p hp
      simpa [orthTensor] using this)
    (fun a b ha hab hcm p hp => by
      obtain ⟨s, hsL, hsa⟩ := C.hA.eich a b ha hab
      have := hstab hsL hsa
        (fun p => by
          simp only [OrthCaseI.orthTensor_one_apply]
          have h1 := LinearEquiv.congr_fun hcm p.1
          have h2 := LinearEquiv.congr_fun hcm p.2
          simp only [LinearEquiv.mul_apply] at h1 h2
          rw [h1, h2]) p hp
      simpa [OrthCaseI.orthTensor_one_apply] using this)
  intro r hr
  obtain ⟨h1, h2⟩ := hspan r hr
  obtain ⟨d, hd, hdr⟩ := (hmemD _).mp (key _ h1 _ h2)
  exact ⟨d, hd, hdr⟩

theorem mul_self_eq_one_of_sub_one_sq {K : Type} [Field K] [CharP K 2]
    {g : Matrix (Fin 2) (Fin 2) K} (h : (g - 1) * (g - 1) = 0) : g * g = 1 := by
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have h2 : ∀ m : Matrix (Fin 2) (Fin 2) K, m + m = 0 := fun m => by
    rw [← two_smul K m, h2K, zero_smul]
  have h3 : (g - 1) * (g - 1) = g * g - (g + g) + 1 := by noncomm_ring
  rw [h3, h2 g, sub_zero] at h
  have h4 : g * g = -1 := eq_neg_of_add_eq_zero_left h
  rw [h4]
  exact (eq_neg_of_add_eq_zero_left (h2 1)).symm

end OrthC5


theorem orth212C5Cond_of (h24 : Smith24ActStatement) (h28 : Smith28OrthStatement)
    (h4 : Orth212C4CondStatement) (hK : OrthClassStatement) : Orth212C5CondStatement := by
  intro G _ _ M Q Z B hc X x hs hD
  obtain ⟨C⟩ := exists_orthCtx h24 hc
  have h7 : Orth212C7CondStatement := orth212C7Cond_of_C4 h4 h28
  rcases hK G M Q Z B hc C X x hs with ⟨g, -, hg1, hgg, hact⟩ | ⟨u, w, hu, hw, huw, hind, hact⟩
  · obtain ⟨h, hhdet, hh⟩ := OrthCaseI.exists_conj_unipotent
      (OrthC5.mul_self_eq_one_of_sub_one_sq hgg) hg1
    have hact' := ActsAsTensor.change hact h (fun a b => rfl) (fun c a => rfl)
    rw [hh] at hact'
    exact OrthC5.core_E hc (C.change h hhdet) hs h4 h28 h7 hD hact'
  · exact OrthC5.core_A hc C hs h4 h28 h7 hD hu hw huw hind hact

end CFSG.RankThree.GF2n.Smith81

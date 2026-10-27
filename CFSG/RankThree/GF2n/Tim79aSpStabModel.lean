module

public import CFSG.ClassicalGroups.Alternating.Generation
public import CFSG.Timmesfeld.Transvection.ModelSpRadical

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Alternating in
theorem spStabGenModel_holds :
    ∀ (n : ℕ) (F : Type) [Field F] (a : Fin n ⊕ Fin n → F), a ≠ 0 →
      ∀ g : StatedSp n F, SpExtras.mat n F g *ᵥ a = a →
        g ∈ Subgroup.closure {x : StatedSp n F | ∃ (b : Fin n ⊕ Fin n → F) (c : F),
          spForm a b = 0 ∧ SpExtras.mat n F x = spTrans b c} := by
  intro n F _ a ha g hga
  set β : LinearMap.BilinForm F (Fin n ⊕ Fin n → F) := Matrix.toBilin' (spGram n F) with hβdef
  have hβ : ∀ x y, β x y = spForm x y := fun x y => Matrix.toBilin'_apply' _ _ _
  have hβa : β.IsAlt := fun x => by rw [hβ]; exact spForm_self x
  have hβn : β.Nondegenerate := by
    rw [hβdef, LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero]
    exact (isUnit_det_of_right_inverse (B := -spGram n F)
      (by rw [Matrix.mul_neg, spGram_mul_self, neg_neg])).ne_zero
  let ρ : StatedSp n F →* LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F) :=
    (Matrix.GeneralLinearGroup.toLin : GL (Fin n ⊕ Fin n) F ≃* _).toMonoidHom.comp
      (StatedSp n F).subtype
  have hρ : ∀ (x : StatedSp n F) (v : Fin n ⊕ Fin n → F),
      ((ρ x : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
        (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F)) v = SpExtras.mat n F x *ᵥ v :=
    fun _ _ => rfl
  have hρinj : Function.Injective ρ := fun x y hxy =>
    Subtype.ext ((Matrix.GeneralLinearGroup.toLin : GL (Fin n ⊕ Fin n) F ≃* _).injective hxy)
  have hiso : ∀ (x : StatedSp n F) (v w : Fin n ⊕ Fin n → F),
      spForm (SpExtras.mat n F x *ᵥ v) (SpExtras.mat n F x *ᵥ w) = spForm v w := by
    intro x v w
    calc spForm (SpExtras.mat n F x *ᵥ v) (SpExtras.mat n F x *ᵥ w)
        = v ⬝ᵥ ((SpExtras.mat n F x)ᵀ *ᵥ (spGram n F *ᵥ (SpExtras.mat n F x *ᵥ w))) := by
          rw [Matrix.dotProduct_mulVec v (SpExtras.mat n F x)ᵀ, Matrix.vecMul_transpose]
      _ = v ⬝ᵥ (((SpExtras.mat n F x)ᵀ * spGram n F * SpExtras.mat n F x) *ᵥ w) := by
          rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec]
      _ = spForm v w := by rw [mat_transpose_mul]
  have h1 : ∀ x : StatedSp n F, ρ x ∈ bilinIsometryGroup β := fun x v w => by
    rw [hρ, hρ, hβ, hβ]
    exact hiso x v w
  set S : Set (StatedSp n F) := {x : StatedSp n F | ∃ (b : Fin n ⊕ Fin n → F) (c : F),
    spForm a b = 0 ∧ SpExtras.mat n F x = spTrans b c}
  have htr : ∀ (w : Fin n ⊕ Fin n → F) (c : F), β a w = 0 →
      symplecticTransvection β hβa w c ∈ Subgroup.closure (ρ '' S) := by
    intro w c hw
    obtain ⟨x, hx⟩ := exists_mat_eq_spTrans w (-c)
    refine Subgroup.subset_closure ⟨x, ⟨w, -c, (hβ a w).symm.trans hw, hx⟩, ?_⟩
    refine Units.ext (LinearMap.ext fun y => ?_)
    rw [hρ, hx, spTrans_mulVec, symplecticTransvection_apply, hβ, spForm_comm w y, neg_mul,
      mul_neg]
  obtain ⟨a', ha'⟩ := exists_spForm_eq_one ha
  have hx : β a a' = 1 := by rw [hβ]; exact ha'
  have hy : β a (SpExtras.mat n F g *ᵥ a') = 1 := by
    have h := hiso g a a'
    rw [hga] at h
    rw [hβ, h, ha']
  obtain ⟨l, -, hlperp, hka, hka'⟩ := alternating_fixed_vector_pair_adjustment hβa hx hy
  set k := (l.map fun p => symplecticTransvection β hβa p.1 p.2).prod
  have hkmem : k ∈ Subgroup.closure (ρ '' S) := by
    refine Subgroup.list_prod_mem _ fun t ht => ?_
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ht
    exact htr p.1 p.2 (hlperp p hp)
  have hkiso : k ∈ bilinIsometryGroup β :=
    closure_symplecticTransvection_le_bilinIsometryGroup hβa
      (list_prod_map_symplecticTransvection_mem_closure hβa l)
  have hinvapp : ∀ (u : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F))
      (x : Fin n ⊕ Fin n → F),
      ((u⁻¹ : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
        (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F))
        ((u : (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F)) x) = x := by
    intro u x
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have hkinva : ((k⁻¹ : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
      (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F)) a = a := by
    have h := hinvapp k a
    rwa [hka] at h
  have hkinva' : ((k⁻¹ : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
      (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F)) (SpExtras.mat n F g *ᵥ a') = a' := by
    have h := hinvapp k a'
    rwa [hka'] at h
  have hqiso : k⁻¹ * ρ g ∈ bilinIsometryGroup β := mul_mem (inv_mem hkiso) (h1 g)
  have hqa : ((k⁻¹ * ρ g : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
      (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F)) a = a := by
    rw [Units.val_mul, Module.End.mul_apply, hρ, hga]
    exact hkinva
  have hqa' : ((k⁻¹ * ρ g : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F)) :
      (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F)) a' = a' := by
    rw [Units.val_mul, Module.End.mul_apply, hρ]
    exact hkinva'
  have hmem := mem_closure_symplecticTransvection_of_apply_eq_of_apply_eq hβa hβn hx hqiso hqa hqa'
  have hmem2 : k⁻¹ * ρ g ∈ Subgroup.closure (ρ '' S) := by
    refine (Subgroup.closure_le _).2 ?_ hmem
    rintro _ ⟨w, hw, c, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw
    exact htr w c (hw a (Submodule.subset_span (Set.mem_insert _ _)))
  have hgmem : ρ g ∈ Subgroup.closure (ρ '' S) := by
    have h := mul_mem hkmem hmem2
    rwa [mul_inv_cancel_left] at h
  rw [← MonoidHom.map_closure] at hgmem
  obtain ⟨x, hxS, hxg⟩ := Subgroup.mem_map.mp hgmem
  obtain rfl := hρinj hxg
  exact hxS

end CFSG.RankThree.GF2n.Tim79a

module

public import CFSG.Milestones.ASVolI.B4Ext.Defs
public import CFSG.Quasithin.Background.SmithB49N4
public import CFSG.Quasithin.Background.SmithB49D5

public section

namespace CFSG.ASVolI

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B5.Ln CFSG.Quasithin.B5.B49 Matrix Module
open CFSG.Open (StatedSL)

section Pullback

theorem burnsideB49x_mem_B1A_of_surjective {Γ G M N : Type*} [Group Γ] [Group G]
    [AddCommGroup M] [AddCommGroup N] {μ : G →* AddMonoid.End M} {ν : Γ →* AddMonoid.End N}
    {σ : Γ →* G} (hσ : Function.Surjective σ) (e : M ≃+ N)
    (he : ∀ γ m, e (μ (σ γ) m) = ν γ (e m)) (hν : ∀ c ∈ Z1A ν, c ∈ B1A ν)
    {δ : G → M} (hδ : δ ∈ Z1A μ) : δ ∈ B1A μ := by
  have hc : (fun γ => e (δ (σ γ))) ∈ Z1A ν := mem_Z1A.2 fun γ γ' => by
    show e (δ (σ (γ * γ'))) = e (δ (σ γ)) + ν γ (e (δ (σ γ')))
    rw [map_mul, mem_Z1A.1 hδ, map_add, he]
  obtain ⟨m, hm⟩ := hν _ hc
  refine ⟨e.symm m, funext fun g => ?_⟩
  obtain ⟨γ, rfl⟩ := hσ g
  apply e.injective
  rw [coboundaryA_apply, map_sub, he, e.apply_symm_apply]
  exact congrFun hm γ

end Pullback

section Coordinates

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {n : ℕ}

theorem burnsideB49x_mulVec_inv (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2))
    (γ : ↥(StatedSL n (ZMod 2))) (v : Fin n → ZMod 2) : M γ *ᵥ (M γ⁻¹ *ᵥ v) = v := by
  rw [mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, one_mulVec]

theorem burnsideB49x_inv_mulVec (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2))
    (γ : ↥(StatedSL n (ZMod 2))) (v : Fin n → ZMod 2) : M γ⁻¹ *ᵥ (M γ *ᵥ v) = v := by
  rw [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec]

@[expose] noncomputable def burnsideB49x_sig (b : W ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2)) :
    ↥(StatedSL n (ZMod 2)) →* (W ≃ₗ[ZMod 2] W) where
  toFun γ := LinearEquiv.ofLinearMap
    ((b.symm : (Fin n → ZMod 2) →ₗ[ZMod 2] W) ∘ₗ (M γ).mulVecLin ∘ₗ (b : W →ₗ[ZMod 2] _))
    ((b.symm : (Fin n → ZMod 2) →ₗ[ZMod 2] W) ∘ₗ (M γ⁻¹).mulVecLin ∘ₗ (b : W →ₗ[ZMod 2] _))
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, mulVecLin_apply,
        LinearEquiv.apply_symm_apply, burnsideB49x_mulVec_inv, LinearEquiv.symm_apply_apply,
        LinearMap.id_apply])
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, mulVecLin_apply,
        LinearEquiv.apply_symm_apply, burnsideB49x_inv_mulVec, LinearEquiv.symm_apply_apply,
        LinearMap.id_apply])
  map_one' := LinearEquiv.ext fun x => by
    show b.symm (M 1 *ᵥ b x) = x
    rw [map_one, one_mulVec, LinearEquiv.symm_apply_apply]
  map_mul' γ δ := LinearEquiv.ext fun x => by
    show b.symm (M (γ * δ) *ᵥ b x) = b.symm (M γ *ᵥ b (b.symm (M δ *ᵥ b x)))
    rw [LinearEquiv.apply_symm_apply, mulVec_mulVec, map_mul]

theorem burnsideB49x_sig_apply (b : W ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2)) (γ : ↥(StatedSL n (ZMod 2)))
    (x : W) : burnsideB49x_sig b M γ x = b.symm (M γ *ᵥ b x) := rfl

theorem burnsideB49x_sig_symm_apply (b : W ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2)) (γ : ↥(StatedSL n (ZMod 2)))
    (x : W) : (burnsideB49x_sig b M γ).symm x = b.symm (M γ⁻¹ *ᵥ b x) := rfl

theorem burnsideB49x_sig_surjective (b : W ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2))
    (hM : ∀ u : GL (Fin n) (ZMod 2), ∃ γ, M γ = u) :
    Function.Surjective (burnsideB49x_sig b M) := by
  intro T
  let L : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) := b.symm.trans (T.trans b)
  obtain ⟨γ, hγ⟩ := hM ⟨LinearMap.toMatrix' L.toLinearMap, LinearMap.toMatrix' L.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp, L.comp_symm, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, L.symm_comp, LinearMap.toMatrix'_id]⟩
  refine ⟨γ, LinearEquiv.ext fun x => ?_⟩
  rw [burnsideB49x_sig_apply, hγ]
  show b.symm (LinearMap.toMatrix' L.toLinearMap *ᵥ b x) = T x
  rw [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
  show b.symm (b (T (b.symm (b x)))) = T x
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

@[expose] noncomputable def burnsideB49x_vecE (n : ℕ) :
    Matrix (Fin n) (Fin n) (ZMod 2) ≃+ (Fin n × Fin n → ZMod 2) :=
  AddEquiv.ofBijective (AddMonoidHom.mk' Matrix.vec Matrix.vec_add) Matrix.vec_bijective

@[expose] noncomputable def burnsideB49x_gramN (b : W ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    (W →ₗ[ZMod 2] W) ≃+ (Fin n × Fin n → ZMod 2) :=
  (((LinearEquiv.arrowCongr b b : (W →ₗ[ZMod 2] W) ≃ₗ[ZMod 2]
      ((Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))).trans
    LinearMap.toMatrix').toAddEquiv).trans (burnsideB49x_vecE n)

theorem burnsideB49x_gramN_apply (b : W ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (f : W →ₗ[ZMod 2] W) :
    burnsideB49x_gramN b f = (LinearMap.toMatrix' (LinearEquiv.arrowCongr b b f)).vec := rfl

theorem burnsideB49x_gramN_muN (b : W ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (γ : ↥(StatedSL n (ZMod 2)))
    (f : W →ₗ[ZMod 2] W) :
    burnsideB49x_gramN b (burnsideB49x_muN W (burnsideB49x_sig b (matHom n) γ) f) =
      muK (matHom n) γ (burnsideB49x_gramN b f) := by
  rw [burnsideB49x_gramN_apply, burnsideB49x_gramN_apply, muK_vec, matHom_apply]
  have h : LinearEquiv.arrowCongr b b
      (burnsideB49x_muN W (burnsideB49x_sig b (matHom n) γ) f) =
      Matrix.toLin' (mat γ) ∘ₗ LinearEquiv.arrowCongr b b f ∘ₗ Matrix.toLin' (mat γ⁻¹) := by
    refine LinearMap.ext fun x => ?_
    rw [LinearEquiv.arrowCongr_apply, burnsideB49x_muN_apply, burnsideB49x_sig_symm_apply,
      LinearEquiv.apply_symm_apply, burnsideB49x_sig_apply, LinearEquiv.apply_symm_apply]
    rfl
  rw [h, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_toLin', Matrix.mul_assoc]

@[expose] noncomputable def burnsideB49x_gramD (b : W ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :
    (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) ≃+ (Fin n × Fin n → ZMod 2) :=
  (((LinearEquiv.arrowCongr b (LinearEquiv.arrowCongr b (LinearEquiv.refl (ZMod 2) (ZMod 2))) :
      (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) ≃ₗ[ZMod 2]
        ((Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)).trans
    (LinearMap.toMatrix₂' (ZMod 2))).toAddEquiv).trans (burnsideB49x_vecE n)

theorem burnsideB49x_gramD_apply (b : W ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) :
    burnsideB49x_gramD b β = (LinearMap.toMatrix₂' (ZMod 2) (LinearEquiv.arrowCongr b
      (LinearEquiv.arrowCongr b (LinearEquiv.refl (ZMod 2) (ZMod 2))) β)).vec := rfl

theorem burnsideB49x_transpose_dmat_inv (γ : ↥(StatedSL n (ZMod 2))) :
    (dmat γ⁻¹)ᵀ = mat γ := by
  rw [dmat, inv_inv, transpose_transpose]

theorem burnsideB49x_gramD_muD (b : W ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (γ : ↥(StatedSL n (ZMod 2)))
    (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) :
    burnsideB49x_gramD b (burnsideB49x_muD W (burnsideB49x_sig b (dmatHom n) γ) β) =
      muK (dmatHom n) γ (burnsideB49x_gramD b β) := by
  rw [burnsideB49x_gramD_apply, burnsideB49x_gramD_apply, muK_vec, dmatHom_apply]
  have h : LinearEquiv.arrowCongr b (LinearEquiv.arrowCongr b (LinearEquiv.refl (ZMod 2) (ZMod 2)))
      (burnsideB49x_muD W (burnsideB49x_sig b (dmatHom n) γ) β) =
      (LinearEquiv.arrowCongr b (LinearEquiv.arrowCongr b (LinearEquiv.refl (ZMod 2) (ZMod 2)))
        β).compl₁₂ (Matrix.toLin' (dmat γ⁻¹)) (Matrix.toLin' (dmat γ⁻¹)) := by
    refine LinearMap.ext₂ fun x y => ?_
    simp only [LinearEquiv.arrowCongr_apply, LinearEquiv.refl_apply, burnsideB49x_muD_apply,
      burnsideB49x_sig_symm_apply, LinearEquiv.apply_symm_apply, LinearMap.compl₁₂_apply,
      Matrix.toLin'_apply, dmatHom_apply]
  rw [h, LinearMap.toMatrix₂'_compl₁₂, LinearMap.toMatrix'_toLin',
    burnsideB49x_transpose_dmat_inv]

end Coordinates

section Base

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem burnsideB49x_baseN (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : Module.finrank (ZMod 2) W = 4)
    {δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W)}
    (hδ : δ ∈ CFSG.Quasithin.JonesParshall.Z1A (burnsideB49x_muN W)) :
    δ ∈ CFSG.Quasithin.JonesParshall.B1A (burnsideB49x_muN W) :=
  let b := (Module.finBasisOfFinrankEq (ZMod 2) W hW).equivFun
  burnsideB49x_mem_B1A_of_surjective
    (burnsideB49x_sig_surjective b (matHom 4) fun u => ⟨ofGL u, rfl⟩)
    (burnsideB49x_gramN b) (burnsideB49x_gramN_muN b) (fun _ hc => h1N4 hc) hδ

theorem burnsideB49x_baseD (W : Type*) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : Module.finrank (ZMod 2) W = 5)
    {δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)}
    (hδ : δ ∈ CFSG.Quasithin.JonesParshall.Z1A (burnsideB49x_muD W)) :
    δ ∈ CFSG.Quasithin.JonesParshall.B1A (burnsideB49x_muD W) :=
  let b := (Module.finBasisOfFinrankEq (ZMod 2) W hW).equivFun
  burnsideB49x_mem_B1A_of_surjective
    (burnsideB49x_sig_surjective b (dmatHom 5) fun u => exists_dmat_eq u)
    (burnsideB49x_gramD b) (burnsideB49x_gramD_muD b) (fun _ hc => h1D5 hc) hδ

end Base

end CFSG.ASVolI

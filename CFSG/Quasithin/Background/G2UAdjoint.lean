module

public import CFSG.Quasithin.Background.G2UColumns

public section

namespace CFSG.Quasithin.G2U

open CFSG.Blueprint.Chevalley

@[expose] def invol (m : List ℕ) (h : mul2 m m = id2) : GL (Fin 14) (ZMod 2) :=
  ⟨dec2 m, dec2 m, by rw [← dec2_mul2, h, dec2_id2], by rw [← dec2_mul2, h, dec2_id2]⟩

@[expose] def gen0 : GL (Fin 14) (ZMod 2) :=
  invol g0c (by decide +kernel)

@[expose] def gen1 : GL (Fin 14) (ZMod 2) :=
  invol g1c (by decide +kernel)

@[expose] def gen2 : GL (Fin 14) (ZMod 2) :=
  invol g2c (by decide +kernel)

@[expose] def gen3 : GL (Fin 14) (ZMod 2) :=
  invol g3c (by decide +kernel)

theorem invol_mul_self (m : List ℕ) (h : mul2 m m = id2) : invol m h * invol m h = 1 :=
  Units.ext (by rw [Units.val_mul, Units.val_one]; exact (invol m h).val_inv)

theorem invol_inv (m : List ℕ) (h : mul2 m m = id2) : (invol m h)⁻¹ = invol m h :=
  inv_eq_of_mul_eq_one_right (invol_mul_self m h)

@[expose] def rootGroup : Subgroup (GL (Fin 14) (ZMod 2)) :=
  Subgroup.closure {gen0, gen1, gen2, gen3}

variable {K L : Type*} [Field K] [CommRing L]

variable (K) in
noncomputable def basisK : Module.Basis (Fin 14) K (RootModule .G2 K) :=
  Finsupp.basisSingleOne.reindex bas.symm

noncomputable def endEquiv (σ : K ≃+* L) :
    Module.End K (RootModule .G2 K) ≃+* Matrix (Fin 14) (Fin 14) L :=
  (LinearMap.toMatrixAlgEquiv (basisK K)).toRingEquiv.trans σ.mapMatrix

theorem endEquiv_apply (σ : K ≃+* L) (f : Module.End K (RootModule .G2 K)) (a b : Fin 14) :
    endEquiv σ f a b = σ (f (Finsupp.single (lab b) 1) (lab a)) := by
  simp only [endEquiv, basisK, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
    RingEquiv.mapMatrix_apply, Matrix.map_apply,
    LinearMap.toMatrixAlgEquiv_apply, Module.Basis.reindex_apply, Equiv.symm_symm,
    Finsupp.coe_basisSingleOne, bas_apply]
  rfl

theorem endEquiv_xOp (σ : K ≃+* L) (i : Fin Tag.G2.rank) (c : K) :
    endEquiv σ (xOp .G2 K i c) = XMat L i (σ c) := by
  ext a b
  rw [endEquiv_apply, xOp_single_apply]
  exact map_colX (σ : K →+* L) i c (lab b) (lab a)

theorem endEquiv_yOp (σ : K ≃+* L) (i : Fin Tag.G2.rank) (c : K) :
    endEquiv σ (yOp .G2 K i c) = YMat L i (σ c) := by
  ext a b
  rw [endEquiv_apply, yOp_single_apply]
  exact map_colY (σ : K →+* L) i c (lab b) (lab a)

noncomputable def glEquiv (σ : K ≃+* L) : ModGL .G2 K ≃* GL (Fin 14) L :=
  Units.mapEquiv (endEquiv σ).toMulEquiv

theorem coe_glEquiv (σ : K ≃+* L) (g : ModGL .G2 K) :
    (glEquiv σ g : Matrix (Fin 14) (Fin 14) L) = endEquiv σ (g : Module.End K _) :=
  Units.coe_mapEquiv _ g

@[expose] noncomputable def glHom (σ : K ≃+* L) : ModGL .G2 K →* GL (Fin 14) L :=
  MonoidHom.ofClass (glEquiv σ)

theorem glHom_apply (σ : K ≃+* L) (g : ModGL .G2 K) : glHom σ g = glEquiv σ g :=
  rfl

theorem glHom_injective (σ : K ≃+* L) : Function.Injective (glHom σ) :=
  (glEquiv σ).injective

private theorem eq_zero_or_one (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t
  decide

private theorem ix_cases (i : Fin Tag.G2.rank) : i = ix 0 ∨ i = ix 1 := by
  revert i
  decide

private theorem mem_rootGroup_of_val {g : GL (Fin 14) (ZMod 2)} (i : Fin Tag.G2.rank)
    (t : ZMod 2) (h : (g : Matrix (Fin 14) (Fin 14) (ZMod 2)) = XMat (ZMod 2) i t ∨
      (g : Matrix (Fin 14) (Fin 14) (ZMod 2)) = YMat (ZMod 2) i t) : g ∈ rootGroup := by
  have hone : g = 1 → g ∈ rootGroup := fun e => e ▸ rootGroup.one_mem
  have hgen : ∀ x ∈ ({gen0, gen1, gen2, gen3} : Set (GL (Fin 14) (ZMod 2))),
      (g : Matrix (Fin 14) (Fin 14) (ZMod 2)) = x → g ∈ rootGroup :=
    fun x hx e => (Units.ext e : g = x) ▸ Subgroup.subset_closure hx
  rcases eq_zero_or_one t with rfl | rfl
  · rcases h with h | h
    · exact hone (Units.ext (h.trans (XMat_zero i)))
    · exact hone (Units.ext (h.trans (YMat_zero i)))
  · rcases ix_cases i with rfl | rfl <;> rcases h with h | h
    · exact hgen gen0 (by simp) (h.trans XMat_zero_one)
    · exact hgen gen2 (by simp) (h.trans YMat_zero_one)
    · exact hgen gen1 (by simp) (h.trans XMat_one_one)
    · exact hgen gen3 (by simp) (h.trans YMat_one_one)

private theorem mem_map_of_val (σ : K ≃+* ZMod 2) (g : GL (Fin 14) (ZMod 2))
    (i : Fin Tag.G2.rank) (h : (g : Matrix (Fin 14) (Fin 14) (ZMod 2)) = XMat (ZMod 2) i 1 ∨
      (g : Matrix (Fin 14) (Fin 14) (ZMod 2)) = YMat (ZMod 2) i 1) :
    g ∈ (adjointGroup .G2 K).map (glHom σ) := by
  refine ⟨(glEquiv σ).symm g, Subgroup.subset_closure ⟨i, 1, ?_⟩, by
    rw [glHom_apply, MulEquiv.apply_symm_apply]⟩
  have hinj := (endEquiv σ).injective
  have hg : endEquiv σ ((glEquiv σ).symm g : Module.End K _) =
      (g : Matrix (Fin 14) (Fin 14) (ZMod 2)) := by
    rw [← coe_glEquiv, MulEquiv.apply_symm_apply]
  rcases h with h | h
  · exact Or.inl (hinj (by rw [hg, h, endEquiv_xOp, map_one]))
  · exact Or.inr (hinj (by rw [hg, h, endEquiv_yOp, map_one]))

theorem map_adjointGroup (σ : K ≃+* ZMod 2) :
    (adjointGroup .G2 K).map (glHom σ) = rootGroup := by
  apply le_antisymm
  · rw [adjointGroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨i, c, h⟩, rfl⟩
    refine mem_rootGroup_of_val i (σ c) ?_
    rw [glHom_apply, coe_glEquiv]
    rcases h with h | h
    · exact Or.inl (by rw [h, endEquiv_xOp])
    · exact Or.inr (by rw [h, endEquiv_yOp])
  · rw [rootGroup, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl | rfl)
    · exact mem_map_of_val σ _ (ix 0) (Or.inl XMat_zero_one.symm)
    · exact mem_map_of_val σ _ (ix 1) (Or.inl XMat_one_one.symm)
    · exact mem_map_of_val σ _ (ix 0) (Or.inr YMat_zero_one.symm)
    · exact mem_map_of_val σ _ (ix 1) (Or.inr YMat_one_one.symm)

theorem map_commutator_adjointGroup (σ : K ≃+* ZMod 2) :
    ⁅adjointGroup .G2 K, adjointGroup .G2 K⁆.map (glHom σ) = ⁅rootGroup, rootGroup⁆ := by
  rw [Subgroup.map_commutator, map_adjointGroup]

noncomputable def commutatorAdjointEquiv (σ : K ≃+* ZMod 2) :
    ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ ≃* ↥⁅rootGroup, rootGroup⁆ :=
  (Subgroup.equivMapOfInjective _ (glHom σ) (glHom_injective σ)).trans
    (MulEquiv.subgroupCongr (map_commutator_adjointGroup σ))

end CFSG.Quasithin.G2U

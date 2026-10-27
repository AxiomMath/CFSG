module

public import CFSG.RankThree.GF2n.Smith81.S81VFrame

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary Module Matrix

variable {F : Type} [Field F] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F}

@[expose] def gLin (g : SUid σ 6) : (Fin 6 → F) →ₗ[F] (Fin 6 → F) :=
  Matrix.mulVecLin ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)

theorem gLin_apply (g : SUid σ 6) (v : Fin 6 → F) : gLin g v = g • v := rfl

theorem gLin_mul (g h : SUid σ 6) (v : Fin 6 → F) : gLin (g * h) v = gLin g (gLin h v) := by
  simp only [gLin, Matrix.mulVecLin_apply, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem gLin_one (v : Fin 6 → F) : gLin (1 : SUid σ 6) v = v := by
  simp [gLin]

theorem herm_gLin (g : SUid σ 6) (x y : Fin 6 → F) : herm σ (gLin g x) (gLin g y) = herm σ x y := by
  exact herm_smul_smul σ g x y

theorem gLin_injective (g : SUid σ 6) : Function.Injective (gLin g) := by
  have h1 : ∀ v, gLin g⁻¹ (gLin g v) = v := fun v => by
    rw [← gLin_mul, inv_mul_cancel, gLin_one]
  intro x y hxy
  calc x = gLin g⁻¹ (gLin g x) := (h1 x).symm
    _ = gLin g⁻¹ (gLin g y) := by rw [hxy]
    _ = y := h1 y

private theorem mat_triple_apply {ι : Type} [Fintype ι] (M J : Matrix ι ι F) (p q : ι) :
    (cT σ M * J * M) p q = ∑ s, σ (M s p) * ∑ t, J s t * M t q := by
  simp only [Matrix.mul_apply, cT_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring)

private theorem conj_dot_mulVec {ι : Type} [Fintype ι] (M : Matrix ι ι F) (u z : ι → F) :
    (fun p => σ ((M *ᵥ u) p)) ⬝ᵥ z = (fun p => σ (u p)) ⬝ᵥ (cT σ M *ᵥ z) := by
  simp only [dotProduct, Matrix.mulVec, cT_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm.trans
    (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun p _ => by ring)

variable (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b)

include hσ hf

noncomputable def gm (g : SUid σ 6) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
  LinearMap.toMatrix (fb hσ hf) (fb hσ hf) (gLin g)

theorem gm_repr (g : SUid σ 6) (x : Fin 6 → F) :
    (fb hσ hf).repr (g • x) = gm hσ hf g *ᵥ (fb hσ hf).repr x := by
  unfold gm
  rw [LinearMap.toMatrix_mulVec_repr]
  rfl

private theorem repr_smul_fam (g : SUid σ 6) (p q : Fin 3 ⊕ Fin 3) :
    (fb hσ hf).repr (g • fam a b p) q = gm hσ hf g q p := by
  rw [← fb_apply hσ hf p, gm_repr, Basis.repr_self, Finsupp.single_eq_pi_single,
    Matrix.mulVec_single_one]
  rfl

theorem gm_mul (g h : SUid σ 6) : gm hσ hf (g * h) = gm hσ hf g * gm hσ hf h := by
  have hl : gLin (g * h) = (gLin g).comp (gLin h) := LinearMap.ext fun v => gLin_mul g h v
  unfold gm
  rw [hl, LinearMap.toMatrix_comp (fb hσ hf) (fb hσ hf) (fb hσ hf)]

theorem gm_one : gm hσ hf (1 : SUid σ 6) = 1 := by
  have hl : gLin (1 : SUid σ 6) = LinearMap.id := LinearMap.ext fun v => gLin_one v
  unfold gm
  rw [hl, LinearMap.toMatrix_id]

private theorem herm_smul_fam_coords (g : SUid σ 6) (p q : Fin 3 ⊕ Fin 3) :
    herm σ (g • fam a b p) (g • fam a b q) =
      ∑ s, σ (gm hσ hf g s p) * ∑ t, Jm F s t * gm hσ hf g t q := by
  rw [herm_eq_coords hσ hf]
  simp only [dotProduct, Matrix.mulVec, repr_smul_fam]

theorem gm_unitary (g : SUid σ 6) : cT σ (gm hσ hf g) * Jm F * gm hσ hf g = Jm F := by
  ext p q
  calc (cT σ (gm hσ hf g) * Jm F * gm hσ hf g) p q
      = ∑ s, σ (gm hσ hf g s p) * ∑ t, Jm F s t * gm hσ hf g t q := mat_triple_apply _ _ _ _
    _ = herm σ (g • fam a b p) (g • fam a b q) := (herm_smul_fam_coords hσ hf g p q).symm
    _ = herm σ (fam a b p) (fam a b q) := herm_smul_smul σ g _ _
    _ = Jm F p q := herm_fam hσ hf p q

theorem gm_det (g : SUid σ 6) : (gm hσ hf g).det = 1 := by
  have h : gLin g = Matrix.toLin' ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) :=
    LinearMap.ext fun v => rfl
  unfold gm
  rw [LinearMap.det_toMatrix, h, LinearMap.det_toLin']
  exact (mem_SUid.mp g.2).1

theorem gm_injective : Function.Injective (gm hσ hf : SUid σ 6 → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
  intro g h hgh
  apply ext_smul σ
  intro v
  have h1 : gLin g = gLin h := by
    apply (LinearMap.toMatrix (fb hσ hf) (fb hσ hf)).injective
    exact hgh
  exact LinearMap.congr_fun h1 v

private theorem ofGm_det (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) (hdet : M.det = 1) :
    (LinearMap.toMatrix' (Matrix.toLin (fb hσ hf) (fb hσ hf) M)).det = 1 := by
  rw [LinearMap.det_toMatrix', LinearMap.det_toLin, hdet]

private theorem ofGm_iso (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
    (hM : cT σ M * Jm F * M = Jm F) :
    ∀ x y, herm σ (LinearMap.toMatrix' (Matrix.toLin (fb hσ hf) (fb hσ hf) M) *ᵥ x)
      (LinearMap.toMatrix' (Matrix.toLin (fb hσ hf) (fb hσ hf) M) *ᵥ y) = herm σ x y := by
  have hrepr : ∀ v, (fb hσ hf).repr (Matrix.toLin (fb hσ hf) (fb hσ hf) M v) =
      M *ᵥ (fb hσ hf).repr v := fun v => by
    rw [← LinearMap.toMatrix_mulVec_repr (fb hσ hf) (fb hσ hf),
      LinearMap.toMatrix_toLin (fb hσ hf) (fb hσ hf)]
  have key : ∀ v : Fin 3 ⊕ Fin 3 → F, cT σ M *ᵥ (Jm F *ᵥ (M *ᵥ v)) = Jm F *ᵥ v := fun v => by
    calc cT σ M *ᵥ (Jm F *ᵥ (M *ᵥ v)) = (cT σ M * Jm F * M) *ᵥ v := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = Jm F *ᵥ v := by rw [hM]
  intro x y
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec,
    herm_eq_coords hσ hf (Matrix.toLin (fb hσ hf) (fb hσ hf) M x)
      (Matrix.toLin (fb hσ hf) (fb hσ hf) M y), herm_eq_coords hσ hf x y,
    hrepr x, hrepr y, conj_dot_mulVec, key]

noncomputable def ofGm (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
    (hM : cT σ M * Jm F * M = Jm F) (hdet : M.det = 1) : SUid σ 6 :=
  mkSU σ (LinearMap.toMatrix' (Matrix.toLin (fb hσ hf) (fb hσ hf) M)) (ofGm_det hσ hf M hdet)
    (ofGm_iso hσ hf M hM)

theorem gm_ofGm (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F)
    (hM : cT σ M * Jm F * M = Jm F) (hdet : M.det = 1) :
    gm hσ hf (ofGm hσ hf M hM hdet) = M := by
  have hg : gLin (ofGm hσ hf M hM hdet) = Matrix.toLin (fb hσ hf) (fb hσ hf) M := by
    apply LinearMap.ext
    intro v
    rw [gLin_apply, ofGm, mkSU_smul, LinearMap.toMatrix'_mulVec]
  unfold gm
  rw [hg, LinearMap.toMatrix_toLin]

theorem smul_fam (g : SUid σ 6) (p : Fin 3 ⊕ Fin 3) :
    g • fam a b p = ∑ q, gm hσ hf g q p • fam a b q := by
  calc g • fam a b p = ∑ q, (fb hσ hf).repr (g • fam a b p) q • fb hσ hf q :=
        ((fb hσ hf).sum_repr _).symm
    _ = ∑ q, gm hσ hf g q p • fam a b q :=
        Finset.sum_congr rfl fun q _ => by rw [repr_smul_fam, fb_apply]

end CFSG.RankThree.GF2n.Smith81.S81V

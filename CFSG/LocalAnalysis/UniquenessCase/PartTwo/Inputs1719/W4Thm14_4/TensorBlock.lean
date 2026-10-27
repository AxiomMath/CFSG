module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.HMultBlock
import CFSG.Certificates.PerfectCoverBound
import CFSG.Quasithin.Background.SmithB51LnReal
import CFSG.GH74.E2.DirectProd
import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.Mult
open scoped Matrix

section Coords

variable {m : ℕ} {K : Type} [Field K] {R : Submodule K (Fin m → K)}

private def blockCol (v : ↥(blockSub (ι := Fin 2) R)) (i : Fin 2) : ↥R :=
  ⟨fun j => Multiplicative.toAdd (v : StdMod (Fin m × Fin 2) K) (j, i), v.2 i⟩

private theorem blockCol_mul (v w : ↥(blockSub (ι := Fin 2) R)) (i : Fin 2) :
    blockCol (v * w) i = blockCol v i + blockCol w i := by
  apply Subtype.ext
  funext j
  simp [blockCol]

private noncomputable def blockCoord (b : Module.Basis (Fin 2) K ↥R)
    (v : ↥(blockSub (ι := Fin 2) R)) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun a i => b.repr (blockCol v i) a

private theorem blockCoord_mul (b : Module.Basis (Fin 2) K ↥R)
    (v w : ↥(blockSub (ι := Fin 2) R)) :
    blockCoord b (v * w) = blockCoord b v + blockCoord b w := by
  ext a i
  simp [blockCoord, blockCol_mul, map_add]

private noncomputable def blockOfMat (b : Module.Basis (Fin 2) K ↥R)
    (M : Matrix (Fin 2) (Fin 2) K) : ↥(blockSub (ι := Fin 2) R) :=
  ⟨Multiplicative.ofAdd fun p => ∑ a, M a p.2 * (b a : Fin m → K) p.1, by
    intro i
    have h : (fun j => ∑ a, M a i * (b a : Fin m → K) j) =
        ((∑ a, M a i • b a : ↥R) : Fin m → K) := by
      funext j
      simp [Pi.smul_apply, smul_eq_mul]
    show (fun j => ∑ a, M a i * (b a : Fin m → K) j) ∈ R
    rw [h, Submodule.coe_sum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (b a).2⟩

private theorem blockCol_blockOfMat (b : Module.Basis (Fin 2) K ↥R)
    (M : Matrix (Fin 2) (Fin 2) K) (i : Fin 2) :
    blockCol (blockOfMat b M) i = ∑ a, M a i • b a := by
  apply Subtype.ext
  funext j
  simp [blockCol, blockOfMat, Pi.smul_apply]

private theorem blockCoord_blockOfMat (b : Module.Basis (Fin 2) K ↥R)
    (M : Matrix (Fin 2) (Fin 2) K) : blockCoord b (blockOfMat b M) = M := by
  ext a i
  rw [blockCoord, Matrix.of_apply, blockCol_blockOfMat, Module.Basis.repr_sum_self]

private noncomputable def blockCoordEquiv (b : Module.Basis (Fin 2) K ↥R) :
    ↥(blockSub (ι := Fin 2) R) ≃* Multiplicative (Matrix (Fin 2) (Fin 2) K) where
  toFun v := Multiplicative.ofAdd (blockCoord b v)
  invFun M := blockOfMat b (Multiplicative.toAdd M)
  left_inv v := by
    apply Subtype.ext
    funext p
    obtain ⟨j, i⟩ := p
    have h : (∑ a, b.repr (blockCol v i) a • b a : ↥R) = blockCol v i :=
      Module.Basis.sum_repr b _
    have h2 : (∑ a, b.repr (blockCol v i) a * (b a : Fin m → K) j) =
        (blockCol v i : Fin m → K) j := by
      have h' := congrArg (fun x : ↥R => (x : Fin m → K) j) h
      rw [Submodule.coe_sum, Finset.sum_apply] at h'
      simpa [Pi.smul_apply, smul_eq_mul] using h'
    show (∑ a, b.repr (blockCol v i) a * (b a : Fin m → K) j) =
      (v : StdMod (Fin m × Fin 2) K) (j, i)
    rw [h2]
    rfl
  right_inv M := by
    apply Multiplicative.toAdd.injective
    show blockCoord b (blockOfMat b (Multiplicative.toAdd M)) = Multiplicative.toAdd M
    rw [blockCoord_blockOfMat]
  map_mul' v w := by rw [blockCoord_mul, ofAdd_add]

end Coords

section Action

variable {m : ℕ} {K : Type} [Field K] {R : Submodule K (Fin m → K)}

private theorem blockCoord_diagGL (b : Module.Basis (Fin 2) K ↥R) (γ : GL (Fin 2) K)
    (v : ↥(blockSub (ι := Fin 2) R))
    (hmem : matAut (diagGL m γ) v ∈ blockSub (ι := Fin 2) R) :
    blockCoord b ⟨matAut (diagGL m γ) v, hmem⟩ =
      blockCoord b v * (γ : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  ext a i
  show b.repr (blockCol (⟨matAut (diagGL m γ) v, hmem⟩ : ↥(blockSub (ι := Fin 2) R)) i) a =
    (blockCoord b v * (γ : Matrix (Fin 2) (Fin 2) K)ᵀ) a i
  rw [Matrix.mul_apply]
  have hcol : blockCol (⟨matAut (diagGL m γ) v, hmem⟩ : ↥(blockSub (ι := Fin 2) R)) i =
      ∑ i' : Fin 2, (γ : Matrix (Fin 2) (Fin 2) K) i i' • blockCol v i' := by
    apply Subtype.ext
    funext j
    simp only [blockCol]
    have h1 : Multiplicative.toAdd (matAut (diagGL m γ) v) =
        toAddMap (matAut (diagGL m γ)) (Multiplicative.toAdd (v : StdMod (Fin m × Fin 2) K)) := rfl
    rw [h1, toAddMap_matAut, diagGL_mulVec]
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [hcol]
  have hrepr : b.repr (∑ i' : Fin 2, (γ : Matrix (Fin 2) (Fin 2) K) i i' • blockCol v i') a =
      ∑ i' : Fin 2, b.repr (blockCol v i') a * (γ : Matrix (Fin 2) (Fin 2) K) i i' := by
    rw [← Module.Basis.coord_apply, map_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [map_smul, smul_eq_mul, Module.Basis.coord_apply, mul_comm]
  rw [hrepr]
  refine Finset.sum_congr rfl fun i' _ => ?_
  show b.repr (blockCol v i') a * (γ : Matrix (Fin 2) (Fin 2) K) i i' =
    (blockCoord b v) a i' * (γ : Matrix (Fin 2) (Fin 2) K)ᵀ i' i
  rw [Matrix.transpose_apply]
  rfl

end Action

section Restrict

variable {m : ℕ} {K : Type} [Field K] {R : Submodule K (Fin m → K)}

private noncomputable def restrLin (B : GL (Fin m) K)
    (hB : ∀ x ∈ R, (B : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R) : ↥R →ₗ[K] ↥R :=
  (Matrix.mulVecLin (B : Matrix (Fin m) (Fin m) K)).restrict hB

private theorem restrLin_apply (B : GL (Fin m) K)
    (hB : ∀ x ∈ R, (B : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R) (v : ↥R) :
    ((restrLin B hB v : ↥R) : Fin m → K) = (B : Matrix (Fin m) (Fin m) K) *ᵥ (v : Fin m → K) :=
  rfl

private noncomputable def restrMat (b : Module.Basis (Fin 2) K ↥R) (B : GL (Fin m) K)
    (hB : ∀ x ∈ R, (B : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R) : Matrix (Fin 2) (Fin 2) K :=
  LinearMap.toMatrix b b (restrLin B hB)

private theorem restrLin_mul {B B' : GL (Fin m) K}
    (hB : ∀ x ∈ R, (B : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R)
    (hB' : ∀ x ∈ R, (B' : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R)
    (hBB' : ∀ x ∈ R, ((B * B' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R) :
    restrLin (B * B') hBB' = restrLin B hB * restrLin B' hB' := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  show ((B * B' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ (v : Fin m → K) =
    (B : Matrix (Fin m) (Fin m) K) *ᵥ ((B' : Matrix (Fin m) (Fin m) K) *ᵥ (v : Fin m → K))
  rw [Units.val_mul, Matrix.mulVec_mulVec]

private theorem restrLin_one
    (h1 : ∀ x ∈ R, ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R) :
    restrLin (1 : GL (Fin m) K) h1 = 1 := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  show ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ (v : Fin m → K) = (v : Fin m → K)
  rw [Units.val_one, Matrix.one_mulVec]

private theorem restrMat_mul (b : Module.Basis (Fin 2) K ↥R) {B B' : GL (Fin m) K}
    (hB : ∀ x ∈ R, (B : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R)
    (hB' : ∀ x ∈ R, (B' : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R)
    (hBB' : ∀ x ∈ R, ((B * B' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R) :
    restrMat b (B * B') hBB' = restrMat b B hB * restrMat b B' hB' := by
  rw [restrMat, restrMat, restrMat, restrLin_mul hB hB' hBB', LinearMap.toMatrix_mul]

private theorem restrMat_one (b : Module.Basis (Fin 2) K ↥R)
    (h1 : ∀ x ∈ R, ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R) :
    restrMat b (1 : GL (Fin m) K) h1 = 1 := by
  rw [restrMat, restrLin_one, LinearMap.toMatrix_one]

private theorem restrMat_congr (b : Module.Basis (Fin 2) K ↥R) {B B' : GL (Fin m) K}
    (hBB' : B = B')
    (hB : ∀ x ∈ R, (B : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R)
    (hB' : ∀ x ∈ R, (B' : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R) :
    restrMat b B hB = restrMat b B' hB' := by
  subst hBB'
  rfl

private theorem blockCoord_kronGL (b : Module.Basis (Fin 2) K ↥R) (B : GL (Fin m) K)
    (hB : ∀ x ∈ R, (B : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R)
    (v : ↥(blockSub (ι := Fin 2) R))
    (hmem : matAut (kronGL (Fin 2) m B) v ∈ blockSub (ι := Fin 2) R) :
    blockCoord b ⟨matAut (kronGL (Fin 2) m B) v, hmem⟩ = restrMat b B hB * blockCoord b v := by
  ext a i
  have hcol : blockCol (⟨matAut (kronGL (Fin 2) m B) v, hmem⟩ : ↥(blockSub (ι := Fin 2) R)) i =
      restrLin B hB (blockCol v i) := by
    apply Subtype.ext
    funext j
    simp only [blockCol]
    have h1 : Multiplicative.toAdd (matAut (kronGL (Fin 2) m B) v) =
        toAddMap (matAut (kronGL (Fin 2) m B))
          (Multiplicative.toAdd (v : StdMod (Fin m × Fin 2) K)) :=
      rfl
    rw [h1, toAddMap_matAut, kronGL_mulVec]
    rw [restrLin_apply]
    simp [Matrix.mulVec, dotProduct]
  have h1 := LinearMap.toMatrix_mulVec_repr b b (restrLin B hB) (blockCol v i)
  show b.repr (blockCol (⟨matAut (kronGL (Fin 2) m B) v, hmem⟩ :
      ↥(blockSub (ι := Fin 2) R)) i) a =
    (restrMat b B hB * blockCoord b v) a i
  rw [hcol, Matrix.mul_apply, ← h1]
  show (LinearMap.toMatrix b b (restrLin B hB) *ᵥ b.repr (blockCol v i)) a =
    ∑ x : Fin 2, (LinearMap.toMatrix b b (restrLin B hB)) a x * b.repr (blockCol v i) x
  simp [Matrix.mulVec, dotProduct]

end Restrict

section Psi

variable {m : ℕ} {K : Type} [Field K] {R : Submodule K (Fin m → K)}
variable {W : Type} [CommGroup W] {L₂ : Subgroup (MulAut W)} {ψ : ↥L₂ →* GL (Fin m) K}

private noncomputable def psiR
    (hRinv : ∀ (y : ↥L₂), ∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R)
    (b : Module.Basis (Fin 2) K ↥R) (y : ↥L₂) : Matrix (Fin 2) (Fin 2) K :=
  restrMat b (ψ y) (hRinv y)

private theorem psiR_mul
    (hRinv : ∀ (y : ↥L₂), ∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R)
    (b : Module.Basis (Fin 2) K ↥R) (y y' : ↥L₂) :
    psiR hRinv b (y * y') = psiR hRinv b y * psiR hRinv b y' := by
  have h3 : ∀ x ∈ R, ((ψ y * ψ y' : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R := by
    rw [← map_mul]
    exact hRinv (y * y')
  refine (restrMat_congr b (map_mul ψ y y') (hRinv (y * y')) h3).trans ?_
  exact restrMat_mul b (hB := hRinv y) (hB' := hRinv y') h3

private theorem psiR_one
    (hRinv : ∀ (y : ↥L₂), ∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R)
    (b : Module.Basis (Fin 2) K ↥R) :
    psiR hRinv b (1 : ↥L₂) = 1 := by
  have h3 : ∀ x ∈ R, ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R := by
    intro x hx
    simpa using hRinv 1 x hx
  refine (restrMat_congr b (map_one ψ) (hRinv 1) h3).trans ?_
  exact restrMat_one b h3

private noncomputable def psiRG
    (hRinv : ∀ (y : ↥L₂), ∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R)
    (b : Module.Basis (Fin 2) K ↥R) : ↥L₂ →* GL (Fin 2) K where
  toFun y :=
    ⟨psiR hRinv b y, psiR hRinv b y⁻¹,
      by rw [← psiR_mul hRinv b y y⁻¹, mul_inv_cancel, psiR_one hRinv b],
      by rw [← psiR_mul hRinv b y⁻¹ y, inv_mul_cancel, psiR_one hRinv b]⟩
  map_one' := Units.ext (psiR_one hRinv b)
  map_mul' y y' := Units.ext (psiR_mul hRinv b y y')

private theorem psiRG_apply
    (hRinv : ∀ (y : ↥L₂), ∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R)
    (b : Module.Basis (Fin 2) K ↥R) (y : ↥L₂) :
    ((psiRG hRinv b y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = psiR hRinv b y := rfl

end Psi

private theorem toAdd_tensorAct {d : ℕ} {K : Type} [Field K]
    (γ : ↥(StatedSL d K) × ↥(StatedSL d K)) (X : Multiplicative (Matrix (Fin d) (Fin d) K)) :
    Multiplicative.toAdd (tensorAct d K γ X) =
      ((γ.1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * Multiplicative.toAdd X *
        ((γ.2 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)ᵀ := by
  simp [tensorAct]

private theorem blockCoord_tensor {m : ℕ} {K : Type} [Field K] {R : Submodule K (Fin m → K)}
    (b : Module.Basis (Fin 2) K ↥R) (γ₁ : Matrix (Fin 2) (Fin 2) K) (γ₂ : GL (Fin 2) K)
    (B : GL (Fin m) K)
    (hB : ∀ x ∈ R, (B : Matrix (Fin m) (Fin m) K) *ᵥ x ∈ R) (hBm : restrMat b B hB = γ₁)
    (X : StdMod (Fin m × Fin 2) K) (hX : X ∈ blockSub (ι := Fin 2) R)
    (hmem : matAut (diagGL m γ₂) (matAut (kronGL (Fin 2) m B) X) ∈
      blockSub (ι := Fin 2) R) :
    blockCoord b ⟨matAut (diagGL m γ₂) (matAut (kronGL (Fin 2) m B) X), hmem⟩ =
      γ₁ * blockCoord b ⟨X, hX⟩ * (γ₂ : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  have hX₁ : matAut (kronGL (Fin 2) m B) X ∈ blockSub (ι := Fin 2) R :=
    matAut_kronGL_mem_blockSub B hB hX
  set Y : ↥(blockSub (ι := Fin 2) R) := ⟨matAut (kronGL (Fin 2) m B) X, hX₁⟩ with hY
  have hYv : (Y : StdMod (Fin m × Fin 2) K) = matAut (kronGL (Fin 2) m B) X := rfl
  have h1 : blockCoord b ⟨matAut (diagGL m γ₂) Y, hmem⟩ = blockCoord b Y * γ₂ᵀ :=
    blockCoord_diagGL b γ₂ Y hmem
  have h2 : blockCoord b Y = restrMat b B hB * blockCoord b ⟨X, hX⟩ :=
    blockCoord_kronGL b B hB ⟨X, hX⟩ hX₁
  rw [show blockCoord b ⟨matAut (diagGL m γ₂) (matAut (kronGL (Fin 2) m B) X), hmem⟩ =
      blockCoord b ⟨matAut (diagGL m γ₂) (Y : StdMod (Fin m × Fin 2) K), hmem⟩ from rfl,
    h1, h2, hBm]

private noncomputable def eUEquiv {W : Type} [CommGroup W] {K : Type} [Field K] {m : ℕ}
    (e : W ≃* StdMod (Fin m × Fin 2) K) (R : Submodule K (Fin m → K)) :
    ↥((blockSub (ι := Fin 2) R).comap e.toMonoidHom) ≃* ↥(blockSub (ι := Fin 2) R) :=
  TauCeti.Subgroup.congrOfMapEq e
    (Subgroup.map_comap_eq_self_of_surjective e.surjective (blockSub (ι := Fin 2) R))

private noncomputable def betaEquiv {W : Type} [CommGroup W] {K : Type} [Field K] {m : ℕ}
    (e : W ≃* StdMod (Fin m × Fin 2) K) (R : Submodule K (Fin m → K))
    (b : Module.Basis (Fin 2) K ↥R) :
    ↥((blockSub (ι := Fin 2) R).comap e.toMonoidHom) ≃*
      Multiplicative (Matrix (Fin 2) (Fin 2) K) :=
  (eUEquiv e R).trans (blockCoordEquiv b)

private theorem eUEquiv_apply {W : Type} [CommGroup W] {K : Type} [Field K] {m : ℕ}
    (e : W ≃* StdMod (Fin m × Fin 2) K) (R : Submodule K (Fin m → K))
    (u : ↥((blockSub (ι := Fin 2) R).comap e.toMonoidHom)) :
    (eUEquiv e R u : ↥(blockSub (ι := Fin 2) R)) =
      ⟨e (u : W), Subgroup.mem_comap.mp u.2⟩ :=
  Subtype.ext (TauCeti.Subgroup.coe_congrOfMapEq_apply e _ u)

private theorem toAdd_betaEquiv {W : Type} [CommGroup W] {K : Type} [Field K] {m : ℕ}
    (e : W ≃* StdMod (Fin m × Fin 2) K) (R : Submodule K (Fin m → K))
    (b : Module.Basis (Fin 2) K ↥R)
    (u : ↥((blockSub (ι := Fin 2) R).comap e.toMonoidHom)) :
    Multiplicative.toAdd (betaEquiv e R b u) = blockCoord b (eUEquiv e R u) := rfl

section Transport

variable {W : Type} [CommGroup W] {K : Type} [Field K] {m : ℕ}
variable {L₁ L₂ : Subgroup (MulAut W)} {e : W ≃* StdMod (Fin m × Fin 2) K}
variable {R : Submodule K (Fin m → K)}

private theorem beta_tensor {π₁ : ↥(StatedSL 2 K) →* ↥L₁}
    (he₁ : ∀ (γ : ↥(StatedSL 2 K)) (w : W),
      e (((π₁ γ : ↥L₁) : MulAut W) w) = matAut (diagGL m (γ : GL (Fin 2) K)) (e w))
    {ψ : ↥L₂ →* GL (Fin m) K}
    (he₂ : ∀ (y : ↥L₂) (w : W),
      e ((y : MulAut W) w) = matAut (kronGL (Fin 2) m (ψ y)) (e w))
    (hRinv : ∀ (y : ↥L₂), ∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R)
    (b : Module.Basis (Fin 2) K ↥R) {ψRse : ↥L₂ ≃* ↥(StatedSL 2 K)}
    (hψinv : ∀ g : ↥(StatedSL 2 K),
      restrMat b (ψ (ψRse.symm g)) (hRinv (ψRse.symm g)) =
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (g₁ g₂ : ↥(StatedSL 2 K)) (u : W) (hu : e u ∈ blockSub (ι := Fin 2) R)
    (hmem : e (((π₁ g₂ : ↥L₁) : MulAut W) (((ψRse.symm g₁ : ↥L₂) : MulAut W) u)) ∈
      blockSub (ι := Fin 2) R) :
    blockCoord b ⟨e (((π₁ g₂ : ↥L₁) : MulAut W) (((ψRse.symm g₁ : ↥L₂) : MulAut W) u)),
        hmem⟩ =
      ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * blockCoord b ⟨e u, hu⟩ *
        ((g₂ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  have hX₁ : matAut (kronGL (Fin 2) m (ψ (ψRse.symm g₁))) (e u) ∈ blockSub (ι := Fin 2) R :=
    matAut_kronGL_mem_blockSub (ψ (ψRse.symm g₁)) (hRinv _) hu
  have hE : e (((π₁ g₂ : ↥L₁) : MulAut W) (((ψRse.symm g₁ : ↥L₂) : MulAut W) u)) =
      matAut (diagGL m (g₂ : GL (Fin 2) K))
        (matAut (kronGL (Fin 2) m (ψ (ψRse.symm g₁))) (e u)) := by
    rw [he₁ g₂ (((ψRse.symm g₁ : ↥L₂) : MulAut W) u), he₂ (ψRse.symm g₁) u]
  have hmem' : matAut (diagGL m (g₂ : GL (Fin 2) K))
      (matAut (kronGL (Fin 2) m (ψ (ψRse.symm g₁))) (e u)) ∈ blockSub (ι := Fin 2) R :=
    matAut_diagGL_mem_blockSub (g₂ : GL (Fin 2) K) hX₁
  have hsub : (⟨e (((π₁ g₂ : ↥L₁) : MulAut W) (((ψRse.symm g₁ : ↥L₂) : MulAut W) u)),
      hmem⟩ : ↥(blockSub (ι := Fin 2) R)) =
      ⟨matAut (diagGL m (g₂ : GL (Fin 2) K))
        (matAut (kronGL (Fin 2) m (ψ (ψRse.symm g₁))) (e u)), hmem'⟩ :=
    Subtype.ext hE
  rw [hsub, blockCoord_tensor b ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
    (g₂ : GL (Fin 2) K) (ψ (ψRse.symm g₁)) (hRinv _) (hψinv g₁) (e u) hu hmem']

end Transport

private theorem pres_left {W : Type} [CommGroup W] {K : Type} [Field K] {m : ℕ}
    {L₁ : Subgroup (MulAut W)} {π₁ : ↥(StatedSL 2 K) →* ↥L₁}
    (hπ₁ : Function.Surjective π₁) (e : W ≃* StdMod (Fin m × Fin 2) K)
    (he₁ : ∀ (γ : ↥(StatedSL 2 K)) (w : W),
      e (((π₁ γ : ↥L₁) : MulAut W) w) = matAut (diagGL m (γ : GL (Fin 2) K)) (e w))
    {R : Submodule K (Fin m → K)} {a : MulAut W} (ha : a ∈ L₁) {u : W}
    (hu : e u ∈ blockSub (ι := Fin 2) R) : e (a u) ∈ blockSub (ι := Fin 2) R := by
  obtain ⟨γ, hγ⟩ := hπ₁ ⟨a, ha⟩
  have h2 := he₁ γ u
  have hγ' : a = ((π₁ γ : ↥L₁) : MulAut W) := (congrArg Subtype.val hγ).symm
  rw [hγ', h2]
  exact matAut_diagGL_mem_blockSub (ι := Fin 2) (k := m) (R := R) γ hu

private theorem pres_right {W : Type} [CommGroup W] {K : Type} [Field K] {m : ℕ}
    {L₂ : Subgroup (MulAut W)} {ψ : ↥L₂ →* GL (Fin m) K} (e : W ≃* StdMod (Fin m × Fin 2) K)
    (he₂ : ∀ (y : ↥L₂) (w : W),
      e ((y : MulAut W) w) = matAut (kronGL (Fin 2) m (ψ y)) (e w))
    {R : Submodule K (Fin m → K)}
    (hRinv : ∀ (y : ↥L₂), ∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R)
    {c : MulAut W} (hc : c ∈ L₂) {u : W} (hu : e u ∈ blockSub (ι := Fin 2) R) :
    e (c u) ∈ blockSub (ι := Fin 2) R := by
  have h2 := he₂ ⟨c, hc⟩ u
  rw [h2]
  exact matAut_kronGL_mem_blockSub (ι := Fin 2) (k := m) (R := R) (ψ ⟨c, hc⟩) (hRinv ⟨c, hc⟩) hu

private theorem blockSub_stable {W : Type} [CommGroup W] {K : Type} [Field K] {m : ℕ}
    {L₁ L₂ : Subgroup (MulAut W)} (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    {e : W ≃* StdMod (Fin m × Fin 2) K} {R : Submodule K (Fin m → K)}
    {π₁ : ↥(StatedSL 2 K) →* ↥L₁} (hπ₁ : Function.Surjective π₁)
    (he₁ : ∀ (γ : ↥(StatedSL 2 K)) (w : W),
      e (((π₁ γ : ↥L₁) : MulAut W) w) = matAut (diagGL m (γ : GL (Fin 2) K)) (e w))
    {ψ : ↥L₂ →* GL (Fin m) K}
    (he₂ : ∀ (y : ↥L₂) (w : W),
      e ((y : MulAut W) w) = matAut (kronGL (Fin 2) m (ψ y)) (e w))
    (hRinv : ∀ (y : ↥L₂), ∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R)
    {x : MulAut W} (hx : x ∈ L₁ ⊔ L₂) {u : W} (hu : e u ∈ blockSub (ι := Fin 2) R) :
    e (x u) ∈ blockSub (ι := Fin 2) R := by
  obtain ⟨a, ha, c, hc, hac⟩ := (CFSG.GH74.E2.mem_sup_iff_of_commute hcomm).1 hx
  rw [← hac, MulAut.mul_apply]
  exact pres_left hπ₁ e he₁ ha (pres_right e he₂ hRinv hc hu)

private noncomputable def piHom {W : Type} [CommGroup W] {K : Type} [Field K]
    {L₁ L₂ : Subgroup (MulAut W)}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) (hdisj : L₁ ⊓ L₂ = ⊥)
    (π₁ : ↥(StatedSL 2 K) →* ↥L₁) (ψRse : ↥L₂ ≃* ↥(StatedSL 2 K)) :
    (↥(StatedSL 2 K) × ↥(StatedSL 2 K)) →* ↥(L₁ ⊔ L₂) :=
  (CFSG.GH74.E2.prodSupEquiv L₁ L₂ hcomm hdisj).toMonoidHom.comp
    (MonoidHom.prod (π₁.comp (MonoidHom.snd _ _))
      (ψRse.symm.toMonoidHom.comp (MonoidHom.fst _ _)))

private theorem piHom_apply {W : Type} [CommGroup W] {K : Type} [Field K]
    {L₁ L₂ : Subgroup (MulAut W)}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) (hdisj : L₁ ⊓ L₂ = ⊥)
    {π₁ : ↥(StatedSL 2 K) →* ↥L₁} (ψRse : ↥L₂ ≃* ↥(StatedSL 2 K))
    (g : ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) (u : W) :
    ((piHom hcomm hdisj π₁ ψRse g : ↥(L₁ ⊔ L₂)) : MulAut W) u =
      ((π₁ g.2 : ↥L₁) : MulAut W) (((ψRse.symm g.1 : ↥L₂) : MulAut W) u) := by
  show ((CFSG.GH74.E2.prodSupEquiv L₁ L₂ hcomm hdisj (π₁ g.2, ψRse.symm g.1) :
    ↥(L₁ ⊔ L₂)) : MulAut W) u = _
  rw [CFSG.GH74.E2.prodSupEquiv_apply, MulAut.mul_apply]

section Identify

variable {W : Type} [CommGroup W] {K : Type} [Field K] [Finite K] {m : ℕ}
variable {L₂ : Subgroup (MulAut W)} {ψ : ↥L₂ →* GL (Fin m) K} {R : Submodule K (Fin m → K)}

private theorem psiR_det {π₂ : ↥(StatedSL 2 K) →* ↥L₂} (hπ₂ : Function.Bijective π₂)
    (hK : Nat.card K = 2 ^ 2) (b : Module.Basis (Fin 2) K ↥R)
    (hRinv : ∀ (y : ↥L₂), ∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R) (y : ↥L₂) :
    (psiR hRinv b y).det = 1 := by
  have hperf : Group.IsPerfect ↥(StatedSL 2 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card (K := K) (by rw [hK]; norm_num)
  obtain ⟨g, rfl⟩ := hπ₂.2 y
  have h := congrArg Units.val (CFSG.Certificates.perfect_hom_comm_trivial
    ((Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K)).comp ((psiRG hRinv b).comp π₂)) g)
  simpa [psiR, psiRG_apply] using h

private theorem exists_psiRse {π₂ : ↥(StatedSL 2 K) →* ↥L₂} (hπ₂ : Function.Bijective π₂)
    (hK : Nat.card K = 2 ^ 2) (b : Module.Basis (Fin 2) K ↥R)
    (hRinv : ∀ (y : ↥L₂), ∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R)
    (hRfaith : ∀ y : ↥L₂, (∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v = v) → y = 1) :
    ∃ ψRse : ↥L₂ ≃* ↥(StatedSL 2 K),
      ∀ g : ↥(StatedSL 2 K),
        restrMat b (ψ (ψRse.symm g)) (hRinv (ψRse.symm g)) =
          ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have hdet : ∀ y : ↥L₂, (psiR hRinv b y).det = 1 := psiR_det hπ₂ hK b hRinv
  have hdet' : ∀ y : ↥L₂, psiRG hRinv b y ∈ StatedSL 2 K := fun y =>
    CFSG.Open.StatedAPI.mem_statedSL_of_det (by rw [psiRG_apply]; exact hdet y)
  let ψRGL : ↥L₂ →* ↥(StatedSL 2 K) :=
    MonoidHom.codRestrict (psiRG hRinv b) (StatedSL 2 K) hdet'
  have hψRGL_apply : ∀ y : ↥L₂,
      ((ψRGL y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = psiR hRinv b y :=
    fun y => psiRG_apply hRinv b y
  have hψRGL_inj : Function.Injective ψRGL := by
    intro y y' hyy'
    have h1 : ψRGL (y * y'⁻¹) = 1 := by rw [map_mul, hyy', map_inv, mul_inv_cancel]
    have h2 : psiR hRinv b (y * y'⁻¹) = 1 := by
      have h := congrArg
        (fun z : ↥(StatedSL 2 K) => ((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h1
      rw [hψRGL_apply] at h
      simpa using h
    have h5 : LinearMap.toMatrix b b (restrLin (ψ (y * y'⁻¹)) (hRinv (y * y'⁻¹))) = 1 :=
      h2
    have h6 : restrLin (ψ (y * y'⁻¹)) (hRinv (y * y'⁻¹)) = 1 :=
      (LinearMap.toMatrix b b).injective (by rw [h5, LinearMap.toMatrix_one])
    have h3 : ∀ v : ↥R, restrLin (ψ (y * y'⁻¹)) (hRinv (y * y'⁻¹)) v = v := by
      intro v
      rw [h6]
      rfl
    have h4 : y * y'⁻¹ = 1 := by
      refine hRfaith (y * y'⁻¹) fun v hv => ?_
      have h := congrArg (fun w : ↥R => (w : Fin m → K)) (h3 ⟨v, hv⟩)
      rw [restrLin_apply] at h
      exact h
    exact mul_inv_eq_one.mp h4
  have : Finite ↥L₂ := Finite.of_surjective π₂ hπ₂.2
  have hψRGL_surj : Function.Surjective ψRGL :=
    (Finite.injective_iff_surjective_of_equiv (Equiv.ofBijective π₂ hπ₂).symm).mp hψRGL_inj
  let ψRse : ↥L₂ ≃* ↥(StatedSL 2 K) := MulEquiv.ofBijective ψRGL ⟨hψRGL_inj, hψRGL_surj⟩
  have hψRse_apply : ∀ y : ↥L₂, ψRse y = ψRGL y :=
    fun y => MulEquiv.ofBijective_apply ψRGL ⟨hψRGL_inj, hψRGL_surj⟩ y
  refine ⟨ψRse, fun g => ?_⟩
  have h2 : ψRGL (ψRse.symm g) = g := by
    rw [← hψRse_apply (ψRse.symm g), MulEquiv.apply_symm_apply]
  have h3 := congrArg
    (fun z : ↥(StatedSL 2 K) => ((z : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h2
  rw [hψRGL_apply] at h3
  simpa [psiR] using h3

end Identify

section Equivariance

variable {W : Type} [CommGroup W] {K : Type} [Field K] {m : ℕ}
variable {L₁ L₂ : Subgroup (MulAut W)} {e : W ≃* StdMod (Fin m × Fin 2) K}
variable {R : Submodule K (Fin m → K)}

private theorem beta_equivariant (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    (hdisj : L₁ ⊓ L₂ = ⊥)
    {π₁ : ↥(StatedSL 2 K) →* ↥L₁}
    (he₁ : ∀ (γ : ↥(StatedSL 2 K)) (w : W),
      e (((π₁ γ : ↥L₁) : MulAut W) w) = matAut (diagGL m (γ : GL (Fin 2) K)) (e w))
    {ψ : ↥L₂ →* GL (Fin m) K}
    (he₂ : ∀ (y : ↥L₂) (w : W),
      e ((y : MulAut W) w) = matAut (kronGL (Fin 2) m (ψ y)) (e w))
    (hRinv : ∀ (y : ↥L₂), ∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R)
    (b : Module.Basis (Fin 2) K ↥R) {ψRse : ↥L₂ ≃* ↥(StatedSL 2 K)}
    (hψinv : ∀ g : ↥(StatedSL 2 K),
      restrMat b (ψ (ψRse.symm g)) (hRinv (ψRse.symm g)) =
        ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (γ : (FFModel.tensorNat 2 K).Gam)
    (u : ↥((blockSub (ι := Fin 2) R).comap e.toMonoidHom))
    (hu : ((piHom hcomm hdisj π₁ ψRse γ : ↥(L₁ ⊔ L₂)) : MulAut W) (u : W) ∈
      (blockSub (ι := Fin 2) R).comap e.toMonoidHom) :
    (betaEquiv e R b).toMonoidHom
        ⟨((piHom hcomm hdisj π₁ ψRse γ : ↥(L₁ ⊔ L₂)) : MulAut W) (u : W), hu⟩ =
      (FFModel.tensorNat 2 K).act γ ((betaEquiv e R b).toMonoidHom u) := by
  obtain ⟨g₁, g₂⟩ := γ
  have hβv : Multiplicative.toAdd ((betaEquiv e R b).toMonoidHom
      ⟨((piHom hcomm hdisj π₁ ψRse (g₁, g₂) : ↥(L₁ ⊔ L₂)) : MulAut W) (u : W), hu⟩) =
      blockCoord b ⟨e (((piHom hcomm hdisj π₁ ψRse (g₁, g₂) : ↥(L₁ ⊔ L₂)) : MulAut W)
        (u : W)), Subgroup.mem_comap.mp hu⟩ := by
    rw [show Multiplicative.toAdd ((betaEquiv e R b).toMonoidHom _) =
      Multiplicative.toAdd (betaEquiv e R b _) from rfl, toAdd_betaEquiv, eUEquiv_apply]
  have hβu : Multiplicative.toAdd ((betaEquiv e R b).toMonoidHom u) =
      blockCoord b ⟨e (u : W), Subgroup.mem_comap.mp u.2⟩ := by
    rw [show Multiplicative.toAdd ((betaEquiv e R b).toMonoidHom u) =
      Multiplicative.toAdd (betaEquiv e R b u) from rfl, toAdd_betaEquiv, eUEquiv_apply]
  have hE : e (((piHom hcomm hdisj π₁ ψRse (g₁, g₂) : ↥(L₁ ⊔ L₂)) : MulAut W) (u : W)) =
      e (((π₁ g₂ : ↥L₁) : MulAut W) (((ψRse.symm g₁ : ↥L₂) : MulAut W) (u : W))) := by
    rw [piHom_apply hcomm hdisj (π₁ := π₁) ψRse (g₁, g₂) (u : W)]
  have hmem' : e (((π₁ g₂ : ↥L₁) : MulAut W)
      (((ψRse.symm g₁ : ↥L₂) : MulAut W) (u : W))) ∈ blockSub (ι := Fin 2) R := by
    rw [← hE]
    exact Subgroup.mem_comap.mp hu
  have hsub : (⟨e (((piHom hcomm hdisj π₁ ψRse (g₁, g₂) : ↥(L₁ ⊔ L₂)) : MulAut W) (u : W)),
      Subgroup.mem_comap.mp hu⟩ : ↥(blockSub (ι := Fin 2) R)) =
      ⟨e (((π₁ g₂ : ↥L₁) : MulAut W) (((ψRse.symm g₁ : ↥L₂) : MulAut W) (u : W))),
        hmem'⟩ := Subtype.ext hE
  have hact2 : Multiplicative.toAdd ((FFModel.tensorNat 2 K).act (g₁, g₂)
      ((betaEquiv e R b).toMonoidHom u)) =
      ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        Multiplicative.toAdd ((betaEquiv e R b).toMonoidHom u) *
          ((g₂ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ :=
    toAdd_tensorAct (d := 2) (K := K) (g₁, g₂) ((betaEquiv e R b).toMonoidHom u)
  apply Multiplicative.toAdd.injective
  rw [hβv, hsub]
  rw [beta_tensor (π₁ := π₁) he₁ he₂ hRinv b hψinv g₁ g₂ (u : W)
    (Subgroup.mem_comap.mp u.2) hmem']
  rw [show blockCoord b ⟨e (u : W), Subgroup.mem_comap.mp u.2⟩ =
      Multiplicative.toAdd ((betaEquiv e R b).toMonoidHom u) from hβu.symm]
  exact hact2.symm

end Equivariance

theorem natTensor_comap_blockSub {W : Type} [CommGroup W] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2) {L₁ L₂ : Subgroup (MulAut W)}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) (hdisj : L₁ ⊓ L₂ = ⊥) {m : ℕ}
    (e : W ≃* StdMod (Fin m × Fin 2) K)
    {π₁ : ↥(StatedSL 2 K) →* ↥L₁} (hπ₁ : Function.Surjective π₁)
    (he₁ : ∀ (γ : ↥(StatedSL 2 K)) (w : W),
      e (((π₁ γ : ↥L₁) : MulAut W) w) = matAut (diagGL m (γ : GL (Fin 2) K)) (e w))
    {π₂ : ↥(StatedSL 2 K) →* ↥L₂} (hπ₂ : Function.Bijective π₂) (ψ : ↥L₂ →* GL (Fin m) K)
    (he₂ : ∀ (y : ↥L₂) (w : W),
      e ((y : MulAut W) w) = matAut (kronGL (Fin 2) m (ψ y)) (e w))
    (R : Submodule K (Fin m → K)) (hR2 : Module.finrank K ↥R = 2)
    (hRinv : ∀ (y : ↥L₂), ∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v ∈ R)
    (hRfaith : ∀ y : ↥L₂, (∀ v ∈ R, (ψ y : Matrix (Fin m) (Fin m) K) *ᵥ v = v) → y = 1) :
    NatTensor (L₁ ⊔ L₂) ((blockSub (ι := Fin 2) R).comap e.toMonoidHom) ⊥ 2 2 := by
  have hfin : Module.Finite K ↥R :=
    Module.Finite.of_injective (Submodule.subtype R) Subtype.val_injective
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 2) K ↥R) :=
    ⟨Module.finBasisOfFinrankEq K ↥R hR2⟩
  obtain ⟨ψRse, hψinv⟩ := exists_psiRse (ψ := ψ) hπ₂ hK b hRinv hRfaith
  refine ⟨K, inferInstance, inferInstance, hK, piHom hcomm hdisj π₁ ψRse, ?_⟩
  have hπ : Function.Surjective (piHom hcomm hdisj π₁ ψRse) := by
    intro x
    obtain ⟨⟨a, c⟩, rfl⟩ := (CFSG.GH74.E2.prodSupEquiv L₁ L₂ hcomm hdisj).surjective x
    obtain ⟨g₂, rfl⟩ := hπ₁ a
    refine ⟨(ψRse c, g₂), ?_⟩
    show CFSG.GH74.E2.prodSupEquiv L₁ L₂ hcomm hdisj (π₁ g₂, ψRse.symm (ψRse c)) = _
    rw [MulEquiv.symm_apply_apply]
  refine CFSG.Quasithin.B5.Ln.realizesVia_of_coord (D := FFModel.tensorNat 2 K) rfl rfl ?_ hπ
    bot_le ?_ ?_ (betaEquiv e R b).toMonoidHom (betaEquiv e R b).surjective ?_
    (beta_equivariant hcomm hdisj he₁ he₂ hRinv b hψinv)
  · intro γ
    refine Multiplicative.toAdd.injective ?_
    show Multiplicative.toAdd (tensorAct 2 K γ (1 : Multiplicative (Matrix (Fin 2) (Fin 2) K))) =
      Multiplicative.toAdd (1 : Multiplicative (Matrix (Fin 2) (Fin 2) K))
    rw [toAdd_tensorAct (d := 2) (K := K) γ (1 : Multiplicative (Matrix (Fin 2) (Fin 2) K))]
    simp
  · intro h u hu
    exact Subgroup.mem_comap.mpr
      (blockSub_stable hcomm hπ₁ he₁ he₂ hRinv h.2 (Subgroup.mem_comap.mp hu))
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro u
    rw [Subgroup.mem_bot]
    change (betaEquiv e R b) u = 1 ↔ (u : W) = 1
    rw [MulEquiv.map_eq_one_iff, OneMemClass.coe_eq_one]

theorem natCard_comap_blockSub {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {m : ℕ} (e : W ≃* StdMod (Fin m × ι) K)
    (R : Submodule K (Fin m → K)) :
    Nat.card ↥((blockSub (ι := ι) R).comap e.toMonoidHom) = Nat.card ↥R ^ Fintype.card ι := by
  have hmap : Nat.card ↥((blockSub (ι := ι) R).map e.symm.toMonoidHom) =
      Nat.card ↥(blockSub (ι := ι) R) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (blockSub (ι := ι) R) e.symm.toMonoidHom
      e.symm.injective).toEquiv.symm
  rw [Subgroup.comap_equiv_eq_map_symm' e, hmap]
  exact natCard_blockSub (ι := ι) R

theorem comap_blockSub_inf_le {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {m n : ℕ} (e : W ≃* StdMod (Fin m × ι) K)
    {R : Fin n → Submodule K (Fin m → K)} (hR : iSupIndep R) (i : Fin n) :
    (blockSub (ι := ι) (R i)).comap e.toMonoidHom ⊓
      (⊥ ⊔ ⨆ (j : Fin n) (_ : j ≠ i), (blockSub (ι := ι) (R j)).comap e.toMonoidHom) ≤ ⊥ := by
  have hY : (⨆ (j : Fin n) (_ : j ≠ i), (blockSub (ι := ι) (R j)).comap e.toMonoidHom) ≤
      (⨆ (j : Fin n) (_ : j ≠ i), blockSub (ι := ι) (R j)).comap e.toMonoidHom :=
    iSup_le fun j => iSup_le fun hj =>
      Subgroup.comap_mono (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  have hker : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  calc (blockSub (ι := ι) (R i)).comap e.toMonoidHom ⊓
        (⊥ ⊔ ⨆ (j : Fin n) (_ : j ≠ i), (blockSub (ι := ι) (R j)).comap e.toMonoidHom)
      ≤ (blockSub (ι := ι) (R i)).comap e.toMonoidHom ⊓
        (⨆ (j : Fin n) (_ : j ≠ i), blockSub (ι := ι) (R j)).comap e.toMonoidHom :=
        inf_le_inf (le_refl _) (sup_le bot_le hY)
    _ = ((blockSub (ι := ι) (R i)) ⊓ ⨆ (j : Fin n) (_ : j ≠ i), blockSub (ι := ι) (R j)).comap
          e.toMonoidHom :=
        (Subgroup.comap_inf _ _ _).symm
    _ ≤ (⊥ : Subgroup (StdMod (Fin m × ι) K)).comap e.toMonoidHom :=
        Subgroup.comap_mono
          (by simpa only [bot_sup_eq] using blockSub_inf_le (ι := ι) (K := K) hR i)
    _ = ⊥ := by rw [MonoidHom.comap_bot, hker]

theorem sup_iSup_comap_blockSub_eq_top {W : Type} [CommGroup W] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] {m n : ℕ} (e : W ≃* StdMod (Fin m × ι) K)
    {R : Fin n → Submodule K (Fin m → K)} (hR : iSup R = ⊤) :
    (⊥ ⊔ ⨆ i, (blockSub (ι := ι) (R i)).comap e.toMonoidHom) = ⊤ := by
  have hgen : (⊥ ⊔ ⨆ i, (blockSub (ι := ι) (R i)).comap e.toMonoidHom) =
      (⊥ ⊔ ⨆ i, blockSub (ι := ι) (R i)).map e.symm.toMonoidHom := by
    simp only [Subgroup.map_sup, Subgroup.map_bot, Subgroup.map_iSup,
      Subgroup.comap_equiv_eq_map_symm' e]
  rw [hgen, sup_iSup_blockSub_eq_top (ι := ι) (K := K) hR]
  exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartA
public import CFSG.Quasithin.Vol2.Ch11SecSFactsCartan
public import CFSG.Quasithin.Vol2.KGNatSp4Levi
public import CFSG.Quasithin.Vol2.KGNatSp4N13

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.Vol2.Ch11.SecS
open CFSG.Quasithin.Vol2.KGNat (IsCoord linModelNat spLine spHyp gmapSp mem_gmapSp
  mat_inv_mulVec mat_mulVec_inv spJ spB_mat spB_single_inl psiSp psiSp_apply)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

namespace C11P9B

variable {K : Type} [Field K]

@[expose] noncomputable def conjT (T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K))
    (g : StatedSp 2 K) : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K) where
  toFun v := mat 2 K g⁻¹ *ᵥ T (mat 2 K g *ᵥ v)
  map_zero' := by simp
  map_add' u v := by simp [Matrix.mulVec_add]

theorem conjT_apply (T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)) (g : StatedSp 2 K)
    (v : Fin 2 ⊕ Fin 2 → K) : conjT T g v = mat 2 K g⁻¹ *ᵥ T (mat 2 K g *ᵥ v) := rfl

theorem conjT_smul {σ : K →+* K} {T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)}
    (hT : ∀ (c : K) x, T (c • x) = σ c • T x) (g : StatedSp 2 K) (c : K)
    (v : Fin 2 ⊕ Fin 2 → K) : conjT T g (c • v) = σ c • conjT T g v := by
  rw [conjT_apply, conjT_apply, Matrix.mulVec_smul, hT, Matrix.mulVec_smul]

theorem conjT_conjT {T T' : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)}
    (h : ∀ x, T (T' x) = x) (g : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K) :
    conjT T g (conjT T' g v) = v := by
  rw [conjT_apply, conjT_apply, mat_mulVec_inv, h, mat_inv_mulVec]

theorem conjT_orth {T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)}
    (hT : ∀ x y, Matrix.toBilin' (spJ K) x y = 0 →
      Matrix.toBilin' (spJ K) (T x) (T y) = 0) (g : StatedSp 2 K) {x y : Fin 2 ⊕ Fin 2 → K}
    (h : Matrix.toBilin' (spJ K) x y = 0) :
    Matrix.toBilin' (spJ K) (conjT T g x) (conjT T g y) = 0 := by
  rw [conjT_apply, conjT_apply, spB_mat]
  exact hT _ _ (by rw [spB_mat]; exact h)

theorem mem_spHyp_of_orth {S : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)}
    (hS : ∀ x y, Matrix.toBilin' (spJ K) x y = 0 →
      Matrix.toBilin' (spJ K) (S x) (S y) = 0) {c : K} (hc : c ≠ 0)
    (he : S (Pi.single (.inl 0) 1) = c • Pi.single (.inl 0) 1) {y : Fin 2 ⊕ Fin 2 → K}
    (hy : y ∈ spHyp K) : S y ∈ spHyp K := by
  have h1 : Matrix.toBilin' (spJ K) y (Pi.single (.inl 0) 1) = 0 := by
    rw [spB_single_inl, neg_eq_zero]
    exact hy
  have h2 := hS _ _ h1
  rw [he, map_smul, spB_single_inl, smul_eq_mul, mul_neg, neg_eq_zero] at h2
  exact (mul_eq_zero.mp h2).resolve_left hc

theorem exists_mat_conjT {T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)}
    (hT : ∀ (c : K) x, T (c • x) = c • T x) (g : StatedSp 2 K) :
    ∃ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, ∀ v, M *ᵥ v = conjT T g v := by
  let L : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := conjT T g
      map_add' := map_add _
      map_smul' := fun c v => by
        rw [conjT_apply, conjT_apply, Matrix.mulVec_smul, hT, Matrix.mulVec_smul]
        rfl }
  exact ⟨LinearMap.toMatrix' L, fun v => LinearMap.toMatrix'_mulVec L v⟩

theorem mat_conj_mulVec (g X : StatedSp 2 K) (x : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (g * X * g⁻¹) *ᵥ x = mat 2 K g *ᵥ (mat 2 K X *ᵥ (mat 2 K g⁻¹ *ᵥ x)) := by
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem mulVec_e0_apply (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (a : Fin 2 ⊕ Fin 2) :
    (X *ᵥ Pi.single (.inl 0) 1) a = X a (.inl 0) := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem blkIdx_mul_of_shape {X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    (hX1 : X (.inl 1) (.inl 0) = 0) (hX2 : X (.inr 1) (.inl 0) = 0)
    (hY1 : Y (.inr 0) (.inl 1) = 0) (hY2 : Y (.inr 0) (.inr 1) = 0) :
    blkIdx (sigma2 0) (X * Y) = blkIdx (sigma2 0) X * blkIdx (sigma2 0) Y := by
  ext i k
  simp only [blkIdx, Matrix.submatrix_apply, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases k <;> simp [sigma2, hX1, hX2, hY1, hY2]

variable {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem conjT_mem_spLine (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (g : StatedSp 2 K) {τ : MulAut W} {T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)}
    (hTf : ∀ w, T (f w) = f (τ w))
    (hU : τ ∈ stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) {v : Fin 2 ⊕ Fin 2 → K}
    (hv : v ∈ spLine K) : conjT T g v ∈ spLine K := by
  obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ v)
  have hw1 : w ∈ hf.pre (gmapSp g (spLine K)).toAddSubgroup := by
    show f w ∈ gmapSp g (spLine K)
    rw [mem_gmapSp, hw, mat_inv_mulVec]
    exact hv
  have h2 : f (τ w) ∈ gmapSp g (spLine K) := (hU w).mp hw1
  rw [mem_gmapSp, ← hTf, hw] at h2
  rw [conjT_apply]
  exact h2

theorem mat_conj_apply (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (g : StatedSp 2 K) {τ : MulAut W} {T T' : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)}
    (hTf : ∀ w, T (f w) = f (τ w)) (hT'f : ∀ w, T' (f w) = f (τ⁻¹ w)) {X X' : StatedSp 2 K}
    (hX' : psiSp π g X' = τ * psiSp π g X * τ⁻¹) (v : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K X' *ᵥ v = conjT T g (mat 2 K X *ᵥ conjT T' g v) := by
  obtain ⟨w, hw⟩ := hf.surj (mat 2 K g *ᵥ v)
  have h1 : f (psiSp π g X' w) = f ((τ * psiSp π g X * τ⁻¹) w) := by rw [hX']
  rw [MulAut.mul_apply, MulAut.mul_apply, ← hTf, psiSp_apply, psiSp_apply, hf.act4, hf.act4,
    ← hT'f, hw, mat_conj_mulVec, mat_conj_mulVec, mat_inv_mulVec] at h1
  rw [conjT_apply, conjT_apply, ← h1, mat_inv_mulVec]

theorem conj_mem_inf_stabW {τ : MulAut W} (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) {U : Subgroup W}
    (hU : τ ∈ stabW U) {h : MulAut W} (hh : h ∈ H ⊓ stabW U) : τ * h * τ⁻¹ ∈ H ⊓ stabW U :=
  ⟨hτH h hh.1, (stabW U).mul_mem ((stabW U).mul_mem hU hh.2) ((stabW U).inv_mem hU)⟩

theorem conj_mem_gammaW {τ : MulAut W} (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) {U : Subgroup W}
    (hU : τ ∈ stabW U) {x : MulAut W} (hx : x ∈ gammaW H U) : τ * x * τ⁻¹ ∈ gammaW H U := by
  have hle : (H ⊓ stabW U).map (MulAut.conj τ).toMonoidHom ≤ H ⊓ stabW U := by
    rintro _ ⟨h, hh, rfl⟩
    exact conj_mem_inf_stabW hτH hU hh
  have h1 := perfectCore_mono hle
  rw [CFSG.Quasithin.Vol2.KGNat.perfectCore_map _ (MulAut.conj τ).injective] at h1
  exact h1 ⟨x, hx, rfl⟩

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA

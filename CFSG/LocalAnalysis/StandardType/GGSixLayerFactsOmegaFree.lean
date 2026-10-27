module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaSplit
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresFinal

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix

section Invol

variable {R : Type*} [Ring R] {T : R → R}

@[expose] def IsInvol.toAddMonoidHom (hT : IsInvol T) : R →+ R where
  toFun := T
  map_zero' := hT.map_zero
  map_add' := hT.map_add

theorem IsInvol.apply_eq_inv (hT : IsInvol T) {u : Rˣ} (hu : u ∈ unitaryOf hT) :
    T (u : R) = ((u⁻¹ : Rˣ) : R) := by
  have h : T (u : R) * (u : R) = 1 := hu
  calc T (u : R) = T (u : R) * ((u * u⁻¹ : Rˣ) : R) := by
        rw [mul_inv_cancel, Units.val_one, mul_one]
    _ = ((u⁻¹ : Rˣ) : R) := by rw [Units.val_mul, ← mul_assoc, h, one_mul]

theorem IsInvol.mul_comm_of_le_unitaryOf (hT : IsInvol T) {A : Subgroup Rˣ}
    (hAU : A ≤ unitaryOf hT) {X : R} (hX : ∀ g ∈ A, X * (g : R) = (g : R) * X) {g : Rˣ}
    (hg : g ∈ A) : T X * (g : R) = (g : R) * T X := by
  have hgi : T ((g⁻¹ : Rˣ) : R) = (g : R) := by
    rw [hT.apply_eq_inv (hAU (A.inv_mem hg)), inv_inv]
  rw [← hgi, ← hT.map_mul, ← hT.map_mul, hX _ (A.inv_mem hg)]

end Invol

section Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

@[expose] noncomputable def gramAdj (M : Matrix ι ι K) (X : Matrix ι ι K) : Matrix ι ι K :=
  M⁻¹ * Xᵀ * M

theorem isInvol_gramAdj {M : Matrix ι ι K} (hM : IsUnit M.det) (hMt : Mᵀ = M) :
    IsInvol (gramAdj M) where
  map_add x y := by simp only [gramAdj, transpose_add, Matrix.mul_add, Matrix.add_mul]
  map_mul x y := by
    simp only [gramAdj, transpose_mul]
    calc M⁻¹ * (yᵀ * xᵀ) * M = M⁻¹ * yᵀ * (M * M⁻¹) * xᵀ * M := by
          rw [mul_nonsing_inv M hM, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  map_one := by simp only [gramAdj, transpose_one, Matrix.mul_one, nonsing_inv_mul M hM]
  invol x := by
    simp only [gramAdj, transpose_mul, transpose_transpose, transpose_nonsing_inv, hMt]
    calc M⁻¹ * (M * (x * M⁻¹)) * M = (M⁻¹ * M) * x * (M⁻¹ * M) := by
          simp only [Matrix.mul_assoc]
      _ = x := by rw [nonsing_inv_mul M hM, Matrix.one_mul, Matrix.mul_one]

theorem gramAdj_smul (M : Matrix ι ι K) (c : K) (X : Matrix ι ι K) :
    gramAdj M (c • X) = c • gramAdj M X := by
  simp only [gramAdj, transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_add_transpose_eq [LinearOrder ι] {M : Matrix ι ι K} (hMt : Mᵀ = M)
    (hd : ∀ i, M i i = 0) : ∃ N : Matrix ι ι K, N + Nᵀ = M := by
  refine ⟨Matrix.of fun i j => if i < j then M i j else 0, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, lt_asymm h]
  · simp [hd]
  · simp only [h, lt_asymm h, ite_true, ite_false, zero_add]
    rw [← Matrix.transpose_apply M i j, hMt]

theorem exists_add_gramAdj_eq_one [LinearOrder ι] {M : Matrix ι ι K} (hM : IsUnit M.det)
    (hMt : Mᵀ = M) (hd : ∀ i, M i i = 0) : ∃ Y : Matrix ι ι K, Y + gramAdj M Y = 1 := by
  obtain ⟨N, hN⟩ := exists_add_transpose_eq hMt hd
  refine ⟨M⁻¹ * N, ?_⟩
  have h1 : gramAdj M (M⁻¹ * N) = M⁻¹ * Nᵀ := by
    simp only [gramAdj, transpose_mul, transpose_nonsing_inv, hMt]
    calc M⁻¹ * (Nᵀ * M⁻¹) * M = M⁻¹ * Nᵀ * (M⁻¹ * M) := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ * Nᵀ := by rw [nonsing_inv_mul M hM, Matrix.mul_one]
  rw [h1, ← Matrix.mul_add, hN, nonsing_inv_mul M hM]

end Gram

section Avg

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

theorem exists_avg_add_eq_one {T : Matrix ι ι K → Matrix ι ι K} (hT : IsInvol T)
    (hTs : ∀ (c : K) X, T (c • X) = c • T X) {A : Subgroup (GL ι K)} (hAU : A ≤ unitaryOf hT)
    (hA : (Nat.card A : K) ≠ 0) {Y₀ : Matrix ι ι K} (hY₀ : Y₀ + T Y₀ = 1) :
    ∃ Y : Matrix ι ι K, (∀ g ∈ A, Y * (g : Matrix ι ι K) = (g : Matrix ι ι K) * Y) ∧
      Y + T Y = 1 := by
  classical
  have : Finite (GL ι K) := inferInstance
  have : Fintype A := Fintype.ofFinite A
  let conjA : Matrix ι ι K → Matrix ι ι K :=
    fun X => ∑ a : A, ((a : GL ι K) : Matrix ι ι K) * X *
      (((a : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K)
  refine ⟨(Nat.card A : K)⁻¹ • conjA Y₀, fun g hg => ?_, ?_⟩
  · have key : (g : Matrix ι ι K) * conjA Y₀ * ((g⁻¹ : GL ι K) : Matrix ι ι K) = conjA Y₀ := by
      simp only [conjA, Finset.mul_sum, Finset.sum_mul]
      refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : A)) _ _ fun a => ?_
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul,
        Matrix.mul_assoc]
    rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    calc conjA Y₀ * (g : Matrix ι ι K)
        = (g : Matrix ι ι K) * conjA Y₀ * ((g⁻¹ : GL ι K) : Matrix ι ι K) *
          (g : Matrix ι ι K) := by rw [key]
      _ = _ := by rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one]
  · have hconj : ∀ a ∈ A, T ((a : Matrix ι ι K) * Y₀ * ((a⁻¹ : GL ι K) : Matrix ι ι K)) =
        (a : Matrix ι ι K) * T Y₀ * ((a⁻¹ : GL ι K) : Matrix ι ι K) := by
      intro a ha
      rw [hT.map_mul, hT.map_mul, hT.apply_eq_inv (hAU ha),
        hT.apply_eq_inv (hAU (A.inv_mem ha)), inv_inv, Matrix.mul_assoc]
    have hadd : conjA Y₀ + T (conjA Y₀) = ∑ _a : A, (1 : Matrix ι ι K) := by
      have h1 : T (conjA Y₀) = conjA (T Y₀) := by
        have := map_sum hT.toAddMonoidHom (fun a : A => ((a : GL ι K) : Matrix ι ι K) * Y₀ *
          (((a : GL ι K)⁻¹ : GL ι K) : Matrix ι ι K)) Finset.univ
        simp only [IsInvol.toAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
        rw [this]
        exact Finset.sum_congr rfl fun a _ => hconj _ a.2
      rw [h1]
      simp only [conjA, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Matrix.add_mul, ← Matrix.mul_add, hY₀, Matrix.mul_one, ← Units.val_mul,
        mul_inv_cancel, Units.val_one]
    rw [hTs, ← smul_add, hadd, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hA, one_smul]

end Avg

section Polar

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] {Q : QuadraticForm K W}

theorem isometry_of_polar {A : Subgroup (W ≃ₗ[K] W)} [Fintype A]
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hA : (Fintype.card A : K) ≠ 0)
    (hfree : ∀ w : W, (∀ a ∈ A, a w = w) → w = 0) {g : W ≃ₗ[K] W}
    (hgc : g ∈ Subgroup.centralizer (A : Set (W ≃ₗ[K] W)))
    (hgB : ∀ x y, polar Q (g x) (g y) = polar Q x y) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  let D : W →+ K :=
    { toFun := fun w => Q (g w) - Q w
      map_zero' := by simp
      map_add' := fun x y => by
        show Q (g (x + y)) - Q (x + y) = (Q (g x) - Q x) + (Q (g y) - Q y)
        rw [map_add, QuadraticMap.map_add Q, QuadraticMap.map_add Q, hgB]
        ring }
  have hDa : ∀ a ∈ A, ∀ w, D (a w) = D w := by
    intro a ha w
    show Q (g (a w)) - Q (a w) = Q (g w) - Q w
    have h1 : g (a w) = a (g w) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply,
        Subgroup.mem_centralizer_iff.mp hgc a ha]
    rw [h1, map_of_mem (hAO ha), map_of_mem (hAO ha)]
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => ?_
  have hsum : ∑ a : A, (a : W ≃ₗ[K] W) w = 0 := hfree _ fun b hb => by
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨b, hb⟩ : A)) _ _ fun a => rfl
  have h2 : D (∑ a : A, (a : W ≃ₗ[K] W) w) = (Fintype.card A : K) * D w := by
    rw [map_sum, Finset.sum_congr rfl fun (a : A) _ => hDa a a.2 w, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  rw [hsum, map_zero] at h2
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2.symm).resolve_left hA)

end Polar

section Transport

open QuadraticMap

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] {ι : Type} [Fintype ι]
  [DecidableEq ι]

@[expose] noncomputable def matEquiv (b : Module.Basis ι K W) : (W ≃ₗ[K] W) ≃* GL ι K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K W).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)

theorem coe_matEquiv (b : Module.Basis ι K W) (g : W ≃ₗ[K] W) :
    (matEquiv b g : Matrix ι ι K) = LinearMap.toMatrix b b (g : W →ₗ[K] W) := rfl

theorem mem_unitaryOf_gramAdj_iff (b : Module.Basis ι K W) {Q : QuadraticForm K W}
    {M : Matrix ι ι K} (hM : M = LinearMap.BilinForm.toMatrix b (polarBilin Q))
    (hMd : IsUnit M.det) (hMt : Mᵀ = M) (g : W ≃ₗ[K] W) :
    matEquiv b g ∈ unitaryOf (isInvol_gramAdj hMd hMt) ↔
      ∀ x y, polar Q (g x) (g y) = polar Q x y := by
  rw [mem_unitaryOf]
  have hcomp : (matEquiv b g : Matrix ι ι K)ᵀ * M * (matEquiv b g : Matrix ι ι K) =
      LinearMap.BilinForm.toMatrix b
        (LinearMap.BilinForm.comp (polarBilin Q) (g : W →ₗ[K] W) (g : W →ₗ[K] W)) := by
    rw [hM, coe_matEquiv, LinearMap.BilinForm.toMatrix_comp b b]
  have h1 : gramAdj M (matEquiv b g : Matrix ι ι K) * (matEquiv b g : Matrix ι ι K) = 1 ↔
      (matEquiv b g : Matrix ι ι K)ᵀ * M * (matEquiv b g : Matrix ι ι K) = M := by
    rw [gramAdj]
    constructor
    · intro h
      have h' : M⁻¹ * ((matEquiv b g : Matrix ι ι K)ᵀ * M * (matEquiv b g : Matrix ι ι K)) = 1 := by
        rw [← h]
        simp only [Matrix.mul_assoc]
      calc (matEquiv b g : Matrix ι ι K)ᵀ * M * (matEquiv b g : Matrix ι ι K)
          = M * (M⁻¹ * ((matEquiv b g : Matrix ι ι K)ᵀ * M * (matEquiv b g : Matrix ι ι K))) := by
            rw [← Matrix.mul_assoc, mul_nonsing_inv M hMd, Matrix.one_mul]
        _ = M := by rw [h', Matrix.mul_one]
    · intro h
      calc M⁻¹ * (matEquiv b g : Matrix ι ι K)ᵀ * M * (matEquiv b g : Matrix ι ι K)
          = M⁻¹ * ((matEquiv b g : Matrix ι ι K)ᵀ * M * (matEquiv b g : Matrix ι ι K)) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h, nonsing_inv_mul M hMd]
  rw [h1, hcomp, hM, (LinearMap.BilinForm.toMatrix b).injective.eq_iff]
  constructor
  · intro h x y
    have := LinearMap.congr_fun₂ h x y
    simpa [polarBilin_apply_apply] using this
  · intro h
    refine LinearMap.ext₂ fun x y => ?_
    simpa [polarBilin_apply_apply] using h x y

end Transport

end LayerCores

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal LayerCores

theorem ggOrthFreeCoreInput_holds : GGOrthFreeCoreInput := by
  intro K _ _ _ W _ _ _ Q hQ A hAO hodd hfree
  classical
  have := finite_linearEquiv (K := K) (V := W)
  have : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_card_ne_zero_of_odd hodd
  set b := Module.finBasis K W with hb
  set M := LinearMap.BilinForm.toMatrix b (polarBilin Q) with hM
  have hMt : Mᵀ = M := by
    ext i j
    rw [Matrix.transpose_apply, hM, LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polarBilin_apply_apply,
      polar_comm]
  have hd : ∀ i, M i i = 0 := fun i => by
    rw [hM, LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polar_self, two_nsmul,
      CharTwo.add_self_eq_zero]
  have hMd : IsUnit M.det :=
    isUnit_iff_ne_zero.mpr ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ)
  have hadj := isInvol_gramAdj hMd hMt
  have hU := mem_unitaryOf_gramAdj_iff b hM hMd hMt
  set A' := A.map (matEquiv b).toMonoidHom with hA'
  have hA'U : A' ≤ unitaryOf hadj := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hU a).mpr (polar_map_of_mem (hAO ha))
  have hcard : (Nat.card A' : K) ≠ 0 := by
    rw [hA', Nat.card_congr (A.equivMapOfInjective _ (matEquiv b).injective).toEquiv.symm]
    exact natCast_card_ne_zero_of_odd hodd
  obtain ⟨Y₀, hY₀⟩ := exists_add_gramAdj_eq_one hMd hMt hd
  obtain ⟨Y, hYc, hY⟩ := exists_avg_add_eq_one hadj (gramAdj_smul M) hA'U hcard hY₀
  obtain ⟨β, S, hS⟩ := exists_coreFamily_adjCent hermCoreInput_holds altCoreInput_holds hcard hadj
    (fun X hX g hg => hadj.mul_comm_of_le_unitaryOf hA'U hX hg) ⟨Y, hYc, hY⟩
  have h := hS.comap (matEquiv b).toMonoidHom (matEquiv b).injective fun g _ =>
    ⟨(matEquiv b).symm g, (matEquiv b).apply_symm_apply g⟩
  have hC : (adjCent A' hadj).comap (matEquiv b).toMonoidHom =
      Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) ⊓ TauCeti.QuadraticMap.orthogonalGroup Q := by
    ext g
    rw [Subgroup.mem_comap, adjCent, Subgroup.mem_inf, Subgroup.mem_inf]
    have hcent : (matEquiv b).toMonoidHom g ∈ Subgroup.centralizer (A' : Set (GL (Fin _) K)) ↔
        g ∈ Subgroup.centralizer (A : Set (W ≃ₗ[K] W)) := by
      rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
      constructor
      · intro h a ha
        exact (matEquiv b).injective (by
          rw [map_mul, map_mul]
          exact h _ ⟨a, ha, rfl⟩)
      · rintro h _ ⟨a, ha, rfl⟩
        show (matEquiv b) a * (matEquiv b) g = (matEquiv b) g * (matEquiv b) a
        rw [← map_mul, ← map_mul, h a ha]
    rw [hcent]
    constructor
    · rintro ⟨hgc, hgu⟩
      exact ⟨hgc, isometry_of_polar hAO hA hfree hgc ((hU g).mp hgu)⟩
    · rintro ⟨hgc, hgO⟩
      exact ⟨hgc, (hU g).mpr (polar_map_of_mem hgO)⟩
  rw [hC] at h
  exact ⟨β, _, h⟩

end CFSG.StandardType

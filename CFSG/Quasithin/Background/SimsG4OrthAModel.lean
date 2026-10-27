module

public import CFSG.Quasithin.Background.SimsG4Core
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms

public section

namespace CFSG.Quasithin.SimsG4

namespace OrthA

section Groups

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

@[expose] def orthGroup (Q : W → K) : Subgroup (W ≃ₗ[K] W) where
  carrier := {φ | ∀ x, Q (φ x) = Q x}
  mul_mem' {φ ψ} hφ hψ x := by
    change Q (φ (ψ x)) = Q x
    rw [hφ, hψ]
  one_mem' _ := rfl
  inv_mem' {φ} hφ x := by
    have h := hφ (φ⁻¹ x)
    rw [mul_inv_apply] at h
    exact h.symm

theorem mem_orthGroup {Q : W → K} {φ : W ≃ₗ[K] W} : φ ∈ orthGroup Q ↔ ∀ x, Q (φ x) = Q x :=
  Iff.rfl

theorem mem_isometryGroup' {q : (Fin 4 → K) → K} {M : Matrix.GeneralLinearGroup (Fin 4) K} :
    M ∈ isometryGroup K q ↔ ∀ v, q ((M : Matrix (Fin 4) (Fin 4) K).mulVec v) = q v :=
  Iff.rfl

@[expose] def subgroupEquiv {G G' : Type*} [Group G] [Group G'] (τ : G ≃* G') {H : Subgroup G}
    {H' : Subgroup G'} (h : ∀ g, g ∈ H ↔ τ g ∈ H') : H ≃* H' where
  toFun g := ⟨τ (g : G), (h g).1 g.2⟩
  invFun g := ⟨τ.symm (g : G'), (h _).2 (by rw [MulEquiv.apply_symm_apply]; exact g.2)⟩
  left_inv g := Subtype.ext (τ.symm_apply_apply (g : G))
  right_inv g := Subtype.ext (τ.apply_symm_apply (g : G'))
  map_mul' g g' := Subtype.ext (map_mul τ (g : G) (g' : G))

theorem mem_isometryGroup_iff (b : Module.Basis (Fin 4) K W) {Q : W → K}
    {q : (Fin 4 → K) → K} (hbq : ∀ v, Q (∑ i, v i • b i) = q v)
    (M : Matrix.GeneralLinearGroup (Fin 4) K) :
    M ∈ isometryGroup K q ↔
      ((Matrix.GeneralLinearGroup.toLin' b).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv K W)) M ∈ orthGroup Q := by
  have hQ : ∀ x, Q x = q (b.repr x) := fun x => by
    conv_lhs => rw [← b.sum_repr x]
    exact hbq _
  have happ : ∀ x, ((Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K W)) M x =
      ∑ i, ((M : Matrix (Fin 4) (Fin 4) K).mulVec (b.repr x)) i • b i := fun x =>
    (Matrix.GeneralLinearGroup.toLin'_apply b M x).trans (Fintype.linearCombination_apply K _ _)
  rw [mem_isometryGroup', mem_orthGroup]
  constructor
  · intro hM x
    rw [happ, hbq, hQ x]
    exact hM _
  · intro hM v
    have h1 := hM (b.equivFun.symm v)
    have h2 : ⇑(b.repr (b.equivFun.symm v)) = v := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [happ, hbq, hQ, h2] at h1
    exact h1

noncomputable def isometryGroupEquiv (b : Module.Basis (Fin 4) K W) {Q : W → K}
    {q : (Fin 4 → K) → K} (hbq : ∀ v, Q (∑ i, v i • b i) = q v) :
    isometryGroup K q ≃* orthGroup Q :=
  subgroupEquiv _ (mem_isometryGroup_iff b hbq)

theorem mem_isometryGroup_map_iff {L : Type} [Field L] (σ : K ≃+* L)
    {qK : (Fin 4 → K) → K} {qL : (Fin 4 → L) → L} (h : ∀ v, qL (fun i => σ (v i)) = σ (qK v))
    (M : Matrix.GeneralLinearGroup (Fin 4) K) :
    M ∈ isometryGroup K qK ↔ Units.mapEquiv σ.mapMatrix.toMulEquiv M ∈ isometryGroup L qL := by
  have hmv : ∀ u : Fin 4 → K,
      ((Units.mapEquiv σ.mapMatrix.toMulEquiv M : Matrix.GeneralLinearGroup (Fin 4) L) :
        Matrix (Fin 4) (Fin 4) L).mulVec (fun i => σ (u i)) =
      fun i => σ (((M : Matrix (Fin 4) (Fin 4) K).mulVec u) i) := by
    intro u
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [mem_isometryGroup', mem_isometryGroup']
  constructor
  · intro hM v
    obtain ⟨u, rfl⟩ : ∃ u : Fin 4 → K, (fun i => σ (u i)) = v :=
      ⟨fun i => σ.symm (v i), funext fun i => σ.apply_symm_apply _⟩
    rw [hmv, h, h, hM u]
  · intro hM u
    have h1 := hM (fun i => σ (u i))
    rw [hmv, h, h] at h1
    exact σ.injective h1

noncomputable def isometryGroupCongr {L : Type} [Field L] (σ : K ≃+* L)
    {qK : (Fin 4 → K) → K} {qL : (Fin 4 → L) → L} (h : ∀ v, qL (fun i => σ (v i)) = σ (qK v)) :
    isometryGroup K qK ≃* isometryGroup L qL :=
  subgroupEquiv _ (mem_isometryGroup_map_iff σ h)

theorem qPlus_map {L : Type} [Field L] (σ : K ≃+* L) (v : Fin 4 → K) :
    qPlus L (fun i => σ (v i)) = σ (qPlus K v) := by
  simp only [qPlus, map_add, map_mul]

theorem qMinus_map {L : Type} [Field L] (σ : K ≃+* L) (c : K) (v : Fin 4 → K) :
    qMinus L (σ c) (fun i => σ (v i)) = σ (qMinus K c v) := by
  simp only [qMinus, map_add, map_mul, map_pow]

end Groups

@[expose] def plusIdx : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![0, 2] ![1, 3]
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

@[expose] def minusIdx : Fin 1 ⊕ Fin 1 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![0] (Sum.elim ![1] ![2, 3])
  invFun := ![Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)]
  left_inv := by decide
  right_inv := by decide

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem exists_basis_normalForm [Finite K] [CharP K 2] (Q : QuadraticForm K W)
    (hdim : Module.finrank K W = 4) (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) :
    (∃ b : Module.Basis (Fin 4) K W, ∀ v, Q (∑ i, v i • b i) = qPlus K v) ∨
      ∃ c : K, (¬ ∃ x : K, x ^ 2 + x + c = 0) ∧
        ∃ b : Module.Basis (Fin 4) K W, ∀ v, Q (∑ i, v i • b i) = qMinus K c v := by
  haveI : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall hnd
  rcases (CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
      Q hQ).2.2.1 2 (by norm_num) (by omega) with ⟨b, hb⟩ | ⟨β, γ, hβ, hroot, b, hb⟩
  · refine Or.inl ⟨b.reindex plusIdx, fun v => ?_⟩
    have e : ∑ i, v i • (b.reindex plusIdx) i =
        ∑ i, ![v 0, v 2] i • b (Sum.inl i) + ∑ i, ![v 1, v 3] i • b (Sum.inr i) := by
      simp only [Module.Basis.reindex_apply, Fin.sum_univ_four, Fin.sum_univ_two]
      simp [plusIdx]
      abel
    rw [e, hb]
    simp [qPlus, Fin.sum_univ_two]
  · obtain ⟨b₁, hb₁⟩ : ∃ b₁ : Module.Basis (Fin 1 ⊕ Fin 1 ⊕ Fin 2) K W,
        ∀ (x y : Fin 1 → K) (s t : K),
          Q (∑ i, x i • b₁ (Sum.inl i) + ∑ i, y i • b₁ (Sum.inr (Sum.inl i)) +
            s • b₁ (Sum.inr (Sum.inr 0)) + t • b₁ (Sum.inr (Sum.inr 1))) =
            ∑ i, x i * y i + s ^ 2 + β * s * t + γ * t ^ 2 := ⟨b, hb⟩
    have hβinv : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ
    refine Or.inr ⟨γ * β⁻¹ ^ 2, ?_, ?_⟩
    · rintro ⟨x, hx⟩
      apply hroot (β * x)
      linear_combination β ^ 2 * hx - γ * (1 + β * β⁻¹) * hβinv
    · have hw : ∀ i, IsUnit (![1, 1, 1, β⁻¹] i : K) := by
        intro i
        fin_cases i <;> simp [hβ]
      refine ⟨(b₁.reindex minusIdx).isUnitSMul hw, fun v => ?_⟩
      have e : ∑ i, v i • ((b₁.reindex minusIdx).isUnitSMul hw) i =
          ∑ i, ![v 0] i • b₁ (Sum.inl i) + ∑ i, ![v 1] i • b₁ (Sum.inr (Sum.inl i)) +
            v 2 • b₁ (Sum.inr (Sum.inr 0)) + (β⁻¹ * v 3) • b₁ (Sum.inr (Sum.inr 1)) := by
        simp only [Module.Basis.isUnitSMul_apply, Module.Basis.reindex_apply, Fin.sum_univ_four,
          Fin.sum_univ_one]
        simp [minusIdx, smul_smul, mul_comm]
      rw [e, hb₁]
      simp only [Fin.sum_univ_one, qMinus]
      simp
      linear_combination (v 2 * v 3) * hβinv

theorem isO4Type_of_orthGroup [Finite K] [CharP K 2] (Q : QuadraticForm K W)
    (hdim : Module.finrank K W = 4) (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    {k : ℕ} (hk : 0 < k) (hK : Nat.card K = 2 ^ k) {X : Type} [Group X]
    (e : X ≃* orthGroup (⇑Q)) : IsO4Type k X := by
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite (GaloisField 2 k)
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 k) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GaloisField.card 2 k hk.ne']
  let σ : K ≃+* GaloisField 2 k := FiniteField.ringEquivOfCardEq hcard
  rcases exists_basis_normalForm Q hdim hnd with ⟨b, hb⟩ | ⟨c, hc, b, hb⟩
  · exact Or.inl ⟨e.trans ((isometryGroupEquiv b hb).symm.trans
      (isometryGroupCongr σ (qPlus_map σ)))⟩
  · refine Or.inr ⟨σ c, ?_, ⟨e.trans ((isometryGroupEquiv b hb).symm.trans
      (isometryGroupCongr σ (qMinus_map σ c)))⟩⟩
    rintro ⟨x, hx⟩
    apply hc
    refine ⟨σ.symm x, σ.injective ?_⟩
    rw [map_add, map_add, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hx

end OrthA

end CFSG.Quasithin.SimsG4

module

public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDTransfer
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFGU2
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFGU3
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDField

public section

namespace CFSG.StandardType

open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.StandardType.TraceFrame

theorem heldGU_herm_mulVec {n : ℕ} {M : Type} [Field M] {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (A : ↥(heldGU n M τ hτ)) (d d' : Fin n → M) :
    ∑ i, τ ((((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d) i) *
        (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d') i =
      ∑ i, τ (d i) * d' i := by
  have hA := (mem_heldGU (a := n) (M := M) (τ := τ) (hτ := hτ)
    (A := (A : GL (Fin n) M))).mp A.2
  have hA' : ((((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M).map (τ : M →+* M))ᵀ *
      ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)) = 1 := hA
  have h := CFSG.LieType.SemisimpleCentralizers.HeldUCD.sum_mulVec_mul_eq (ρ := (τ : M →+* M))
    (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)) d d'
  rw [hA'] at h
  simpa [Matrix.mulVec, dotProduct, Matrix.one_apply] using h


private lemma rhoGL_mem {K M V U : Type} [Field K] [Finite K] [Field M] [Finite M]
    [Algebra K M] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} {n : ℕ} {B : LinearMap.BilinForm K V}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    (hB : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ (0, w)) (Φ (0, w')))
    (A : ↥(heldGU n M τ hτ)) :
    rhoGL Φ (A : GL (Fin n) M) ∈ sesqUnitaryGroup B := by
  rw [mem_sesqUnitaryGroup]
  intro x y
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective x
  obtain ⟨⟨d', w'⟩, rfl⟩ := Φ.surjective y
  simp only [coe_rhoGL, LinearEquiv.coe_coe]
  calc
    B (rhoEquiv Φ (A : GL (Fin n) M) (Φ (d, w)))
        (rhoEquiv Φ (A : GL (Fin n) M) (Φ (d', w')))
        = B (Φ ((((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d), w))
            (Φ ((((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d'), w')) := by
          rw [rhoEquiv_apply, rhoEquiv_apply]
    _ = ∑ i, Algebra.trace K M
          (τ ((((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d) i) *
            (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d') i) +
          B (Φ (0, w)) (Φ (0, w')) := hB _ _ _ _
    _ = ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ (0, w)) (Φ (0, w')) := by
          congr 1
          rw [← map_sum, heldGU_herm_mulVec A d d', map_sum]
    _ = B (Φ (d, w)) (Φ (d', w')) := (hB d d' w w').symm

private noncomputable def rho {K M V U : Type} [Field K] [Finite K] [Field M] [Finite M]
    [Algebra K M] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} {n : ℕ} {B : LinearMap.BilinForm K V}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    (hB : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ (0, w)) (Φ (0, w'))) :
    ↥(heldGU n M τ hτ) →* ↥(sesqUnitaryGroup B) where
  toFun A := ⟨rhoGL Φ (A : GL (Fin n) M), rhoGL_mem hB A⟩
  map_one' := by
    apply Subtype.ext
    change rhoGL Φ (1 : GL (Fin n) M) = 1
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm
      (rhoEquiv Φ (1 : GL (Fin n) M)) = 1
    rw [rhoEquiv_one, map_one]
  map_mul' A B := by
    apply Subtype.ext
    change rhoGL Φ ((A : GL (Fin n) M) * (B : GL (Fin n) M)) =
      rhoGL Φ (A : GL (Fin n) M) * rhoGL Φ (B : GL (Fin n) M)
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm
        (rhoEquiv Φ ((A : GL (Fin n) M) * (B : GL (Fin n) M))) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm
        (rhoEquiv Φ (A : GL (Fin n) M)) *
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm
        (rhoEquiv Φ (B : GL (Fin n) M))
    rw [rhoEquiv_mul, map_mul]

private lemma coe_rho {K M V U : Type} [Field K] [Finite K] [Field M] [Finite M]
    [Algebra K M] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} {n : ℕ} {B : LinearMap.BilinForm K V}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    {hB : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ (0, w)) (Φ (0, w'))}
    (A : ↥(heldGU n M τ hτ)) :
    ((rho hB A : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) =
      rhoGL Φ (A : GL (Fin n) M) := rfl

private lemma rho_apply {K M V U : Type} [Field K] [Finite K] [Field M] [Finite M]
    [Algebra K M] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} {n : ℕ} {B : LinearMap.BilinForm K V}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    {hB : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ (0, w)) (Φ (0, w'))}
    (A : ↥(heldGU n M τ hτ)) (d : Fin n → M) (w : U) :
    (((rho hB A : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
      (Φ (d, w)) = Φ (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d, w) := by
  change ((rhoGL Φ (A : GL (Fin n) M) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
      (Φ (d, w)) = Φ (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d, w)
  rw [coe_rhoGL]
  simp only [LinearEquiv.coe_coe, rhoEquiv_apply]

private lemma rho_injective {K M V U : Type} [Field K] [Finite K] [Field M] [Finite M]
    [Algebra K M] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {τ : M ≃+* M} {hτ : ∀ y, τ (τ y) = y} {n : ℕ} {B : LinearMap.BilinForm K V}
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    {hB : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ (0, w)) (Φ (0, w'))} :
    Function.Injective (rho (τ := τ) (hτ := hτ) (n := n) (B := B) (Φ := Φ) hB) := by
  intro A A' hAA'
  have hlin : (rhoEquiv Φ (A : GL (Fin n) M) : V →ₗ[K] V) =
      (rhoEquiv Φ (A' : GL (Fin n) M) : V →ₗ[K] V) := by
    have h := congrArg (fun u : ↥(sesqUnitaryGroup B) =>
      ((u : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)) hAA'
    rw [coe_rho, coe_rho] at h
    simpa only [coe_rhoGL] using h
  have hvec : ∀ d : Fin n → M, ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d =
      ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d := by
    intro d
    have h := congrArg (fun f : V →ₗ[K] V => f (Φ (d, 0))) hlin
    simpa [rhoEquiv_apply] using h
  have hmat : ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) =
      ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    simpa [Matrix.mulVec_single_one] using hvec (Pi.single j 1)
  exact Subtype.ext (Units.ext hmat)

private lemma frob_conj {K M V U : Type} [Field K] [Finite K] [Field M] [Finite M]
    [Algebra K M] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    {τ : M ≃+* M} (hK : Nat.card K = 2) {hτ : ∀ y, τ (τ y) = y} {n : ℕ}
    {B : LinearMap.BilinForm K V} {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    (hB : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ (0, w)) (Φ (0, w')))
    (i : Fin n) (A A' : ↥(heldGU n M τ hτ))
    (hvec : ∀ d : Fin n → M,
      Function.update
          (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ Function.update d i (τ (d i)))
          i (τ ((((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ
            Function.update d i (τ (d i))) i)) =
        ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d) :
    (⟨frobUnit hK hτ Φ i, frobUnit_mem hK hτ hB i⟩ : ↥(sesqUnitaryGroup B)) *
        rho hB A *
        (⟨frobUnit hK hτ Φ i, frobUnit_mem hK hτ hB i⟩ : ↥(sesqUnitaryGroup B))⁻¹ =
      rho hB A' := by
  have hf : (⟨frobUnit hK hτ Φ i, frobUnit_mem hK hτ hB i⟩ : ↥(sesqUnitaryGroup B))⁻¹ =
      ⟨frobUnit hK hτ Φ i, frobUnit_mem hK hτ hB i⟩ := by
    apply Subtype.ext
    exact frobUnit_inv hK hτ i
  rw [hf]
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro v
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  rw [Module.End.mul_apply, Module.End.mul_apply]
  simp only [coe_rho, coe_rhoGL, LinearEquiv.coe_coe]
  rw [coe_frobUnit_apply, coe_frobUnit_apply]
  simp only [frobEquivV_apply, rhoEquiv_apply]
  rw [hvec d]


theorem exists_heldGU_rep_of_traceFrame {K M V U : Type} [Field K] [Finite K] [Field M]
    [Finite M] [Algebra K M] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
    (hK : Nat.card K = 2) (hM : Nat.card M = 4) {τ : M ≃+* M} (hτ : ∀ y, τ (τ y) = y)
    {n : ℕ} {B : LinearMap.BilinForm K V}
    (Φ : ((Fin n → M) × U) ≃ₗ[K] V)
    (hB : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, Algebra.trace K M (τ (d i) * d' i) + B (Φ (0, w)) (Φ (0, w'))) :
    ∃ ρ : ↥(heldGU n M τ hτ) →* ↥(sesqUnitaryGroup B), Function.Injective ρ ∧
      (∀ (A : ↥(heldGU n M τ hτ)) d w,
        (((ρ A : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
          (Φ (d, w)) = Φ (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d, w)) ∧
      (∀ i : Fin n, ∃ f : ↥(sesqUnitaryGroup B),
        (∀ d w, (((f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
          (Φ (d, w)) = Φ (Function.update d i (τ (d i)), w)) ∧
        (∀ A A' : ↥(heldGU n M τ hτ),
          (∀ j k, j ≠ k → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j k = 0) →
          (∀ j k, j ≠ k → ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j k = 0) →
          ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
            τ (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i) →
          (∀ j, j ≠ i → ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j j =
            ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j j) →
          f * ρ A * f⁻¹ = ρ A') ∧
        ∀ A : ↥(heldGU n M τ hτ),
          (∀ j, j ≠ i → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0 ∧
            ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j i = 0) →
          ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i = 1 → f * ρ A * f⁻¹ = ρ A) ∧
      ∀ (s g : ↥(sesqUnitaryGroup B)) (c : M), c ^ 2 ≠ c →
        (∀ d w, (((s : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
          (Φ (d, w)) = Φ (c • d, w)) →
        g * s = s * g →
        ∃ (A : ↥(heldGU n M τ hτ)) (g₀ : U →ₗ[K] U), ∀ d w,
          (((g : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
            (Φ (d, w)) = Φ (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) *ᵥ d, g₀ w) := by
  refine ⟨rho hB, rho_injective (τ := τ) (hτ := hτ) (n := n) (B := B) (Φ := Φ) (hB := hB),
    ?_, ?_, ?_⟩
  · intro A d w
    exact rho_apply (Φ := Φ) (hB := hB) A d w
  · intro i
    refine ⟨⟨frobUnit hK hτ Φ i, frobUnit_mem hK hτ hB i⟩, ?_, ?_, ?_⟩
    · intro d w
      exact frobUnit_apply hK hτ i d w
    · intro A A' hdiag hdiag' hii hjj
      refine frob_conj (hτ := hτ) (B := B) (Φ := Φ) hK hB i A A' fun d => ?_
      exact frob_diag_vec hK hτ hdiag hdiag' hii hjj d
    · intro A htriv hii
      refine frob_conj (hτ := hτ) (B := B) (Φ := Φ) hK hB i A A fun d => ?_
      exact frob_trivial_vec (K := K) hτ (fun j hj => (htriv j hj).1)
        (fun j hj => (htriv j hj).2) hii d
  · intro s g c hc hs hcomm
    exact sesq_centralizer_form hK hM hB hc hs hcomm

end CFSG.StandardType

end

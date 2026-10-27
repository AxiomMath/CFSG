module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFGU2
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFTorus2
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.StandardType.NormFrame

open CFSG.Assembly
open CFSG.StandardType.QTwoFrameTorus
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable def normFrameFrob {K M U V : Type} [Field K] [Finite K]
    [Field M] [Algebra K M] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    {n : ℕ} {τ : M ≃+* M} (hK : Nat.card K = 2)
    (Φ : ((Fin n → M) × U) ≃ₗ[K] V) : V ≃ₗ[K] V :=
  (Φ.symm.trans (((LinearEquiv.piCongrRight fun _ : Fin n =>
      (TraceFrame.tauAlg (τ := τ) hK).toLinearEquiv).prodCongr
        (LinearEquiv.refl K U)))).trans Φ

noncomputable def normFrameTorus {K M U V : Type} [Field K] [Finite K]
    [Field M] [Algebra K M] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    {n : ℕ} (Φ : ((Fin n → M) × U) ≃ₗ[K] V) (u : Fin n → Mˣ) : V ≃ₗ[K] V :=
  TraceFrame.rhoEquiv Φ (TauCeti.diagGL u)

lemma normFrameFrob_apply {K M U V : Type} [Field K] [Finite K]
    [Field M] [Algebra K M] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    {n : ℕ} {τ : M ≃+* M} (hK : Nat.card K = 2)
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} (d : Fin n → M) (w : U) :
    normFrameFrob (τ := τ) hK Φ (Φ (d, w)) = Φ (fun i => τ (d i), w) := by
  rw [normFrameFrob, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  congr 1

lemma normFrameTorus_apply {K M U V : Type} [Field K] [Finite K]
    [Field M] [Algebra K M] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    {n : ℕ} {Φ : ((Fin n → M) × U) ≃ₗ[K] V} (u : Fin n → Mˣ)
    (d : Fin n → M) (w : U) :
    normFrameTorus Φ u (Φ (d, w)) = Φ (fun i => (u i : M) * d i, w) := by
  rw [normFrameTorus, TraceFrame.rhoEquiv_apply, TauCeti.diagGL_coe]
  congr 1
  refine Prod.ext ?_ rfl
  funext i
  change ((Matrix.diagonal fun j => (u j : M)).mulVec d) i = (u i : M) * d i
  simp [Matrix.mulVec_diagonal]

lemma normFrameFrob_mul_self {K M U V : Type} [Field K] [Finite K]
    [Field M] [Finite M] [Algebra K M] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {n : ℕ} {τ : M ≃+* M} (hK : Nat.card K = 2)
    (hM : Nat.card M = 4) (hτ : ∀ y, τ y = y ^ 2)
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} :
    normFrameFrob (τ := τ) hK Φ * normFrameFrob (τ := τ) hK Φ = 1 := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  rw [LinearEquiv.mul_apply, normFrameFrob_apply (τ := τ), normFrameFrob_apply (τ := τ)]
  change Φ (fun i => τ (τ (d i)), w) = Φ (d, w)
  congr 1
  refine Prod.ext ?_ rfl
  funext i
  exact frame_tau_tau hM hτ (d i)

lemma normFrameTorus_pow_three {K M U V : Type} [Field K] [Finite K]
    [Field M] [Algebra K M] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    {n : ℕ} {Φ : ((Fin n → M) × U) ≃ₗ[K] V} {u : Fin n → Mˣ}
    (hu : ∀ i, (u i : M) ^ 3 = 1) :
    normFrameTorus Φ u ^ 3 = 1 := by
  have hu' : u ^ 3 = 1 := by
    funext i
    exact Units.ext (hu i)
  have hA : TauCeti.diagGL u ^ 3 = 1 := by
    rw [← map_pow, hu', map_one]
  have hcalc : normFrameTorus Φ u ^ 3 =
      TraceFrame.rhoEquiv Φ (TauCeti.diagGL u ^ 3) := by
    rw [pow_three', pow_three', normFrameTorus, TraceFrame.rhoEquiv_mul,
      TraceFrame.rhoEquiv_mul]
  rw [hcalc, hA, TraceFrame.rhoEquiv_one]

lemma normFrameTorus_mem_orthogonal {K M U V : Type} [Field K] [Finite K]
    [Field M] [Finite M] [Algebra K M] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {n : ℕ} {Q : QuadraticForm K V}
    {τ : M ≃+* M} (hτ : ∀ y, τ y = y ^ 2) {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    (hN : ∀ d w, algebraMap K M (Q (Φ (d, w))) =
      ∑ i, τ (d i) * d i + algebraMap K M (Q (Φ (0, w))))
    {u : Fin n → Mˣ} (hu : ∀ i, (u i : M) ^ 3 = 1) :
    normFrameTorus Φ u ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  rw [normFrameTorus_apply]
  apply (algebraMap K M).injective
  rw [hN (fun i => (u i : M) * d i) w, hN d w]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hu3 : (u i : M) ^ 2 * (u i : M) = 1 := by
    rw [show (u i : M) ^ 2 * (u i : M) = (u i : M) ^ 3 by ring, hu i]
  calc τ ((u i : M) * d i) * ((u i : M) * d i)
      = (τ (u i) * (u i : M)) * (τ (d i) * d i) := by
        rw [map_mul]; ring
    _ = τ (d i) * d i := by rw [hτ (u i), hu3, one_mul]

lemma normFrameFrob_mem_orthogonal {K M U V : Type} [Field K] [Finite K]
    [Field M] [Finite M] [Algebra K M] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {n : ℕ} {Q : QuadraticForm K V}
    {τ : M ≃+* M} (hK : Nat.card K = 2) (hM : Nat.card M = 4)
    (hτ : ∀ y, τ y = y ^ 2) {Φ : ((Fin n → M) × U) ≃ₗ[K] V}
    (hN : ∀ d w, algebraMap K M (Q (Φ (d, w))) =
      ∑ i, τ (d i) * d i + algebraMap K M (Q (Φ (0, w)))) :
    normFrameFrob (τ := τ) hK Φ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  rw [normFrameFrob_apply (τ := τ)]
  apply (algebraMap K M).injective
  rw [hN (fun i => τ (d i)) w, hN d w]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frame_tau_tau hM hτ (d i)]
  ring

lemma normFrameFrob_commutator_torus {K M U V : Type} [Field K] [Finite K]
    [Field M] [Finite M] [Algebra K M] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {n : ℕ} {τ : M ≃+* M} (hK : Nat.card K = 2)
    (hM : Nat.card M = 4) (hτ : ∀ y, τ y = y ^ 2)
    {Φ : ((Fin n → M) × U) ≃ₗ[K] V} {u : Fin n → Mˣ} :
    ⁅normFrameFrob (τ := τ) hK Φ, normFrameTorus Φ u⁆ = normFrameTorus Φ u := by
  classical
  have hr : (normFrameFrob (τ := τ) hK Φ)⁻¹ = normFrameFrob (τ := τ) hK Φ :=
    inv_eq_of_mul_eq_one_left (normFrameFrob_mul_self hK hM hτ)
  have ht_inv : ∀ d w, (normFrameTorus Φ u)⁻¹ (Φ (d, w)) =
      Φ (fun i => (u i : M)⁻¹ * d i, w) := by
    intro d w
    have h : normFrameTorus Φ u (Φ (fun i => (u i : M)⁻¹ * d i, w)) = Φ (d, w) := by
      rw [normFrameTorus_apply]
      congr 1
      refine Prod.ext ?_ rfl
      funext i
      change (u i : M) * ((u i : M)⁻¹ * d i) = d i
      rw [← mul_assoc, mul_inv_cancel₀ (u i).ne_zero, one_mul]
    rw [← h]
    exact (normFrameTorus Φ u).left_inv _
  rw [commutatorElement_def, hr]
  apply LinearEquiv.ext
  intro v
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  have hcoord : ∀ i : Fin n,
      τ ((u i : M) * τ ((u i : M)⁻¹ * d i)) = (u i : M) * d i := by
    intro i
    calc τ ((u i : M) * τ ((u i : M)⁻¹ * d i))
        = τ (u i) * ((u i : M)⁻¹ * d i) := by
          rw [map_mul, frame_tau_tau hM hτ]
      _ = (u i : M) * d i := by
          rw [hτ (u i)]
          have hne : (u i : M) ≠ 0 := (u i).ne_zero
          field_simp
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    ht_inv, normFrameFrob_apply (τ := τ), normFrameTorus_apply,
    normFrameFrob_apply (τ := τ), normFrameTorus_apply]
  congr 1
  refine Prod.ext ?_ rfl
  funext i
  exact hcoord i

end CFSG.StandardType.NormFrame

end

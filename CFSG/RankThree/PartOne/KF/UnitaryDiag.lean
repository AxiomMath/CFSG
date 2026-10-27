module

public import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane

variable {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

include h in
theorem exists_isPrimitiveRoot (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ p := by
  have hfin := h.finite
  have hdvd : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    have h2 : ℓ ^ (2 * f) = ℓ ^ f * ℓ ^ f := by rw [two_mul, pow_add]
    have h3 : ℓ ^ f * ℓ ^ f - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have := Nat.mul_self_sub_mul_self_eq (ℓ ^ f) 1
      simpa using this
    rw [h2, h3]
    exact Dvd.dvd.mul_right hpq _
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzp : IsPrimitiveRoot z p := by
    have := IsPrimitiveRoot.orderOf z
    rwa [hz] at this
  exact ⟨(z : K), IsPrimitiveRoot.coe_units_iff.mpr hzp⟩

theorem exists_unitary_conj_diag (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1)
    (G : Subgroup (primeFormUnitary h (idGram K n)))
    (hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) (hpow : ∀ x ∈ G, x ^ p = 1) :
    ∃ P : primeFormUnitary h (idGram K n), ∀ x ∈ G,
      (((P⁻¹ * x * P : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K).IsDiag := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot h hp hpq
  have hfinK : Finite K := h.finite
  let F : ↥G → Module.End K (Fin n → K) := fun x =>
    ((toLinU h n (x : primeFormUnitary h (idGram K n)) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K))
  have hFcomm : ∀ x y : ↥G, Commute (F x) (F y) := fun x y => by
    have h1 : Commute (toLinU h n (x : primeFormUnitary h (idGram K n)))
        (toLinU h n (y : primeFormUnitary h (idGram K n))) := by
      have := congrArg (toLinU h n) (hcomm x x.2 y y.2)
      rw [map_mul, map_mul] at this
      exact this
    exact h1.units_val
  have hFpow : ∀ x : ↥G, F x ^ p = 1 := fun x => by
    have h1 : toLinU h n ((x : primeFormUnitary h (idGram K n)) ^ p) = 1 := by
      rw [hpow x x.2, map_one]
    rw [map_pow] at h1
    have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (u : Module.End K (Fin n → K))) h1
    simpa [F] using h2
  have hFiso : ∀ (x : ↥G) (v w : Fin n → K), idForm h n (F x v) (F x w) = idForm h n v w :=
    fun x v w => (mem_sesqUnitaryGroup.mp
      (toLinU_mem (x : primeFormUnitary h (idGram K n)))) v w
  obtain ⟨b, μ, hbμ, hon⟩ := exists_orthonormal_common_eigenbasis h hζ hpq
    (idForm_isSymm h n) (idForm_separatingLeft h n) F hFcomm hFpow hFiso
  let e := finCongr (Module.finrank_fin_fun (n := n) K)
  let b' : Module.Basis (Fin n) K (Fin n → K) := b.reindex e
  have hb' : ∀ k, b' k = b (e.symm k) := fun k => by
    simp [b', Module.Basis.reindex_apply]
  let Pm : Matrix (Fin n) (Fin n) K := Matrix.of fun r k => b' k r
  have hPm : (Pm.map h.bar)ᵀ * Pm = 1 := by
    ext k l
    have h1 := hon (e.symm k) (e.symm l)
    rw [← hb', ← hb', gramForm_apply] at h1
    simp only [idGram, Units.val_one, Matrix.one_mulVec] at h1
    have h2 : (if e.symm k = e.symm l then (1 : K) else 0) = if k = l then 1 else 0 := by
      simp [e.symm.injective.eq_iff]
    rw [h2] at h1
    simpa [Matrix.mul_apply, Matrix.one_apply, Pm, dotProduct] using h1
  have hPm' : Pm * (Pm.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hPm
  let P : primeFormUnitary h (idGram K n) :=
    ⟨⟨Pm, (Pm.map h.bar)ᵀ, hPm', hPm⟩, by
      rw [mem_primeFormUnitary]
      simpa [idGram] using hPm⟩
  refine ⟨P, fun x hx => ?_⟩
  have hxP : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Pm =
      Pm * diagonal (fun k => μ ⟨x, hx⟩ (e.symm k)) := by
    ext r k
    have h1 := hbμ ⟨x, hx⟩ (e.symm k)
    have h2 := congrFun h1 r
    rw [← hb'] at h2
    have h3 : (F ⟨x, hx⟩ (b' k)) r =
        (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b' k) r := rfl
    rw [h3] at h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have h4 : (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Pm) r k =
        (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ b' k) r := rfl
    rw [Matrix.mul_diagonal, h4, h2]
    change _ = b' k r * _
    ring
  have : ((P⁻¹ * x * P : primeFormUnitary h (idGram K n)) : GL (Fin n) K) =
      ((P : GL (Fin n) K)⁻¹ * (x : GL (Fin n) K) * (P : GL (Fin n) K)) := rfl
  rw [this, Units.val_mul, Units.val_mul, Matrix.mul_assoc]
  change (((P : GL (Fin n) K)⁻¹ : GL (Fin n) K).val *
    (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Pm)).IsDiag
  rw [hxP, ← Matrix.mul_assoc]
  have hP1 : (((P : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Pm = 1 :=
    Units.inv_mul _
  rw [hP1, Matrix.one_mul]
  exact Matrix.isDiag_diagonal _


theorem unitarySU_le_primeFormUnitary :
    unitarySU ℓ f K n ≤ primeFormUnitary h (idGram K n) := fun g hg => by
  have := ((mem_unitarySU_iff h).mp hg).2
  rw [mem_primeFormUnitary]
  simpa [idGram] using this

theorem conj_mem_unitarySU {P : GL (Fin n) K} (hP : P ∈ primeFormUnitary h (idGram K n))
    {g : GL (Fin n) K} (hg : g ∈ unitarySU ℓ f K n) : P * g * P⁻¹ ∈ unitarySU ℓ f K n := by
  rw [unitarySU_eq_gramSU h n, mem_gramSU_iff_unitary] at hg ⊢
  refine ⟨mul_mem (mul_mem hP hg.1) (inv_mem hP), ?_⟩
  have h1 := hg.2
  have h2 : ((P * g * P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      ((P : Matrix (Fin n) (Fin n) K)).det * ((g : Matrix (Fin n) (Fin n) K)).det *
        ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det := by
    simp only [Units.val_mul, Matrix.det_mul]
  rw [h2, h1, mul_one, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.det_one]

@[expose] noncomputable def conjSU (P : primeFormUnitary h (idGram K n)) :
    unitarySU ℓ f K n ≃* unitarySU ℓ f K n where
  toFun g := ⟨(P : GL (Fin n) K) * g * (P : GL (Fin n) K)⁻¹, conj_mem_unitarySU h P.2 g.2⟩
  invFun g := ⟨(P : GL (Fin n) K)⁻¹ * g * (P : GL (Fin n) K), by
    have := conj_mem_unitarySU h (inv_mem P.2) g.2
    simpa using this⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  map_mul' g g' := Subtype.ext (by simp [mul_assoc])

theorem coe_conjSU (P : primeFormUnitary h (idGram K n)) (g : unitarySU ℓ f K n) :
    ((conjSU h P g : unitarySU ℓ f K n) : GL (Fin n) K) =
      (P : GL (Fin n) K) * g * (P : GL (Fin n) K)⁻¹ := rfl

end CFSG.RankThree.PartOne.KFU

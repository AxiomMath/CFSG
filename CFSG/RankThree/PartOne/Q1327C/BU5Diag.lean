module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.PartOne.KC.UnitaryOrthonormalEigenbasis
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.Q1327C

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KFU

variable {ℓ f n m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

include h in
theorem exists_unitary_conj_diag_m [NeZero m] {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    (hmq : m ∣ ℓ ^ f + 1) (G : Subgroup (primeFormUnitary h (idGram K n)))
    (hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) (hpow : ∀ x ∈ G, x ^ m = 1) :
    ∃ P : primeFormUnitary h (idGram K n), ∀ x ∈ G,
      (((P⁻¹ * x * P : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K).IsDiag := by
  classical
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
  have hFpow : ∀ x : ↥G, F x ^ m = 1 := fun x => by
    have h1 : toLinU h n ((x : primeFormUnitary h (idGram K n)) ^ m) = 1 := by
      rw [hpow x x.2, map_one]
    rw [map_pow] at h1
    have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (u : Module.End K (Fin n → K))) h1
    simpa [F] using h2
  have hFiso : ∀ (x : ↥G) (v w : Fin n → K), idForm h n (F x v) (F x w) = idForm h n v w :=
    fun x v w => (mem_sesqUnitaryGroup.mp
      (toLinU_mem (x : primeFormUnitary h (idGram K n)))) v w
  obtain ⟨b, μ, hbμ, hon⟩ := exists_orthonormal_common_eigenbasis h hζ hmq
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

end CFSG.RankThree.PartOne.Q1327C

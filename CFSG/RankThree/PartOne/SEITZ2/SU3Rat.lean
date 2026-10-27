module

public import CFSG.RankThree.PartOne.SEITZ2.SU3Tv

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

section Phi

variable {K : Type} [Field K] {k : Subfield K} {σ : K ≃+* K} {σ₀ : k ≃+* k}

@[expose] def incl {n : ℕ} (v : Fin n → k) : Fin n → K := fun i => (v i : K)

theorem conjTr_map_subtype (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) k) :
    conjTr σ (M.map k.subtype) = (conjTr σ₀ M).map k.subtype := by
  ext i j
  simp [conjTr, hσk]

theorem herm_incl (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) {n : ℕ} (x y : Fin n → k) :
    herm σ (incl x) (incl y) = ((herm σ₀ x y : k) : K) := by
  simp [herm, incl, hσk]

@[expose] noncomputable def phi (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) :
    SUid σ₀ 3 →* SUid σ 3 where
  toFun g := ⟨Units.map (RingHom.mapMatrix k.subtype).toMonoidHom g.1, by
    obtain ⟨hdet, hu⟩ := g.2
    refine ⟨?_, ?_⟩
    · change (k.subtype.mapMatrix (g.1 : Matrix (Fin 3) (Fin 3) k)).det = 1
      rw [← RingHom.map_det, hdet, map_one]
    · change conjTr σ ((g.1 : Matrix (Fin 3) (Fin 3) k).map k.subtype) *
        ((g.1 : Matrix (Fin 3) (Fin 3) k).map k.subtype) = 1
      rw [conjTr_map_subtype hσk, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g g' := Subtype.ext (by simp)

theorem coe_phi (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) (g : SUid σ₀ 3) :
    (((phi hσk g : SUid σ 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).map k.subtype := rfl

theorem phi_smul (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) (g : SUid σ₀ 3)
    (v : Fin 3 → k) : phi hσk g • incl v = incl (g • v) := by
  rw [smul_def, smul_def, coe_phi]
  funext i
  simp [incl, Matrix.mulVec, dotProduct]

theorem isTv_phi (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) {t : SUid σ₀ 3} {a : Fin 3 → k}
    {c : k} (h : IsTv σ₀ t a c) : IsTv σ (phi hσk t) (incl a) (c : K) := by
  have hincl : ∀ j : Fin 3, incl (Pi.single j (1 : k)) = (Pi.single j (1 : K) : Fin 3 → K) := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij
      simp [incl]
    · simp [incl, hij]
  have hM : ((phi hσk t : SUid σ 3) : GL (Fin 3) K).val = tvMat σ (incl a) (c : K) := by
    apply Matrix.ext_of_mulVec_single
    intro j
    have h1 : phi hσk t • incl (Pi.single j (1 : k)) =
        incl (Pi.single j (1 : k)) + ((c : K) * herm σ (incl a) (incl (Pi.single j (1 : k)))) •
          incl a := by
      rw [phi_smul hσk, h]
      funext i
      simp [incl, herm_incl hσk]
    rw [hincl j] at h1
    rw [tvMat_mulVec]
    exact h1
  intro w
  rw [smul_def, hM, tvMat_mulVec]

end Phi

section ConjU

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem herm_unitary_mulVec {A : Matrix (Fin n) (Fin n) K} (hA : conjTr σ A * A = 1)
    (x y : Fin n → K) : herm σ (A *ᵥ x) (A *ᵥ y) = herm σ x y := by
  rw [herm_mulVec, hA, one_mulVec]

@[expose] noncomputable def conjU (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1) :
    SUid σ n →* SUid σ n where
  toFun g := ⟨A * g.1 * A⁻¹, by
    rw [mem_SUid_iff σ]
    obtain ⟨hdet, hiso⟩ := (mem_SUid_iff σ).1 g.2
    have hAA : ∀ v : Fin n → K, (A : Matrix (Fin n) (Fin n) K) *ᵥ
        (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := fun v => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
    refine ⟨?_, fun x y => ?_⟩
    · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one,
        ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    · have hx : ((A * g.1 * A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
          (A : Matrix (Fin n) (Fin n) K) *ᵥ ((g.1 : Matrix (Fin n) (Fin n) K) *ᵥ
            (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x)) := by
        rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have hy : ((A * g.1 * A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y =
          (A : Matrix (Fin n) (Fin n) K) *ᵥ ((g.1 : Matrix (Fin n) (Fin n) K) *ᵥ
            (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ y)) := by
        rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [hx, hy, herm_unitary_mulVec hA, hiso, ← herm_unitary_mulVec hA, hAA, hAA]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g g' := Subtype.ext (by
    show A * (g.1 * g'.1) * A⁻¹ = (A * g.1 * A⁻¹) * (A * g'.1 * A⁻¹)
    group)

theorem mulVec_inv_mulVec (A : GL (Fin n) K) (v : Fin n → K) :
    (A : Matrix (Fin n) (Fin n) K) *ᵥ (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem conjU_smul (A : GL (Fin n) K)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1)
    (g : SUid σ n) (v : Fin n → K) :
    conjU A hA g • v = (A : Matrix (Fin n) (Fin n) K) *ᵥ
      (g • (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)) := by
  rw [smul_def, smul_def]
  show ((A * g.1 * A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = _
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem IsTv.conjU {A : GL (Fin n) K}
    {hA : conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1}
    {t : SUid σ n} {a : Fin n → K} {c : K} (h : IsTv σ t a c) :
    IsTv σ (conjU A hA t) ((A : Matrix (Fin n) (Fin n) K) *ᵥ a) c := by
  intro v
  rw [conjU_smul, h, Matrix.mulVec_add, Matrix.mulVec_smul, mulVec_inv_mulVec]
  congr 3
  rw [← herm_unitary_mulVec hA a, mulVec_inv_mulVec]

end ConjU

end CFSG.RankThree.PartOne.SEITZ2

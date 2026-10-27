module

public import CFSG.RankThree.PartOne.KC.UnitaryNonregularDefs
public import CFSG.RankThree.PartOne.KC.UnitaryTransvection

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryTrv

@[expose] def nrL (K : Type) [Field K] : Submodule K (Fin 4 → K) where
  carrier := {w | w 2 = 0 ∧ w 3 = 0}
  add_mem' := fun {a b} ha hb => ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' := fun c x hx => ⟨by simp [hx.1], by simp [hx.2]⟩

namespace KCUnitaryNr

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem mem_nrL {w : Fin 4 → K} : w ∈ nrL K ↔ w 2 = 0 ∧ w 3 = 0 := Iff.rfl

theorem gramForm_nrA (x y : Fin 4 → K) :
    gramForm h (nrGramA K) x y =
      h.bar (x 0) * y 2 + h.bar (x 1) * y 3 + h.bar (x 2) * y 0 + h.bar (x 3) * y 1 := by
  simp [gramForm_apply, dotProduct, mulVec, Fin.sum_univ_four, nrGramA]

theorem nrGramA_barTranspose : ((nrGramA K).map h.bar)ᵀ = nrGramA K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nrGramA]

theorem gramForm_nrA_symm : (gramForm h (nrGramA K)).IsSymm :=
  gramForm_isSymm h (nrGramA_barTranspose h)

theorem nrL_iso : ∀ v ∈ nrL K, ∀ w ∈ nrL K, gramForm h (nrGramA K) v w = 0 := by
  intro v hv w hw
  rw [gramForm_nrA, hv.1, hv.2, hw.1, hw.2]
  simp

theorem mem_orthogonalBilin_nrL {y : Fin 4 → K} :
    y ∈ (nrL K).orthogonalBilin (gramForm h (nrGramA K)) ↔ y 2 = 0 ∧ y 3 = 0 := by
  rw [Submodule.mem_orthogonalBilin]
  constructor
  · intro hy
    have h0 := hy (Pi.single 0 1) ⟨by simp, by simp⟩
    have h1 := hy (Pi.single 1 1) ⟨by simp, by simp⟩
    rw [gramForm_nrA] at h0 h1
    simp at h0 h1
    exact ⟨h0, h1⟩
  · intro hy w hw
    rw [gramForm_nrA, hw.1, hw.2, hy.1, hy.2]
    simp

theorem nrA_diag (A : Matrix (Fin 4) (Fin 4) K) (σ : K ≃+* K) {η : K} (hη : h.bar η = -η)
    (hη0 : η ≠ 0) (hση : σ η ≠ 0) (j j' : Fin 4) (hjL : (Pi.single j 1 : Fin 4 → K) ∈ nrL K)
    (hH : ∀ x : Fin 4 → K, gramForm h (nrGramA K) (Pi.single j 1) x = x j')
    (hΦ : ∀ (w y : Fin 4 → K) (c : K), w ∈ nrL K →
      y ∈ (nrL K).orthogonalBilin (gramForm h (nrGramA K)) →
      c + h.bar c = -gramForm h (nrGramA K) y y → ∀ x : Fin 4 → K,
      semilin A σ (eichlerMatrix h (nrGramA K) w y c *ᵥ x) =
        eichlerMatrix h (nrGramA K) w y c *ᵥ semilin A σ x) :
    ∃ κ : K, semilin A σ (Pi.single j 1) = κ • (Pi.single j 1 : Fin 4 → K) ∧
      ∀ x : Fin 4 → K, semilin A σ x j' = σ η / η * κ * σ (x j') := by
  have h0 : η + h.bar η = -gramForm h (nrGramA K) (0 : Fin 4 → K) 0 := by
    rw [hη, add_neg_cancel]
    simp
  have key : ∀ x : Fin 4 → K,
      σ (η * x j') • semilin A σ (Pi.single j 1) =
        (η * semilin A σ x j') • (Pi.single j 1 : Fin 4 → K) := by
    intro x
    have h1 := hΦ (Pi.single j 1) 0 η hjL (zero_mem _) h0 x
    rw [eichlerMatrix_mulVec, eichlerMatrix_mulVec] at h1
    simp only [hH, smul_zero, add_zero, map_zero, LinearMap.zero_apply, zero_smul, sub_zero] at h1
    rw [semilin_add, semilin_smul] at h1
    exact add_left_cancel h1
  have hjj : (Pi.single j' 1 : Fin 4 → K) j' = 1 := by simp
  obtain ⟨κ, hκ⟩ : ∃ κ : K, semilin A σ (Pi.single j 1) = κ • (Pi.single j 1 : Fin 4 → K) := by
    refine ⟨(σ η)⁻¹ * (η * semilin A σ (Pi.single j' 1) j'), ?_⟩
    have h1 := key (Pi.single j' 1)
    rw [hjj, mul_one] at h1
    calc semilin A σ (Pi.single j 1) = (σ η)⁻¹ • σ η • semilin A σ (Pi.single j 1) := by
          rw [smul_smul, inv_mul_cancel₀ hση, one_smul]
      _ = _ := by rw [h1, smul_smul]
  refine ⟨κ, hκ, fun x => ?_⟩
  have h1 := congrFun (key x) j
  rw [hκ] at h1
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, map_mul] at h1
  field_simp
  linear_combination h1.symm


theorem gramForm_nrA_e0 (x : Fin 4 → K) : gramForm h (nrGramA K) (Pi.single 0 1) x = x 2 := by
  rw [gramForm_nrA]
  simp

theorem gramForm_nrA_e1 (x : Fin 4 → K) : gramForm h (nrGramA K) (Pi.single 1 1) x = x 3 := by
  rw [gramForm_nrA]
  simp

theorem gramForm_nrA_smul_e1 (a : K) (x : Fin 4 → K) :
    gramForm h (nrGramA K) (a • (Pi.single 1 1 : Fin 4 → K)) x = h.bar a * x 3 := by
  rw [map_smulₛₗ, LinearMap.smul_apply, gramForm_nrA_e1, smul_eq_mul]

theorem nrA_pointwise (A : GL (Fin 4) K) (hA : A ∈ primeFormUnitary h (nrGramA K))
    (σ : K ≃+* K)
    (hΦ : ∀ (w y : Fin 4 → K) (c : K), w ∈ nrL K →
      y ∈ (nrL K).orthogonalBilin (gramForm h (nrGramA K)) →
      c + h.bar c = -gramForm h (nrGramA K) y y → ∀ x : Fin 4 → K,
      semilin (A : Matrix (Fin 4) (Fin 4) K) σ (eichlerMatrix h (nrGramA K) w y c *ᵥ x) =
        eichlerMatrix h (nrGramA K) w y c *ᵥ semilin (A : Matrix (Fin 4) (Fin 4) K) σ x) :
    (∀ t, σ t = t) ∧ ∃ κ : K, κ ≠ 0 ∧ h.norm κ = 1 ∧ ∀ i j : Fin 4,
      ¬ (i.val < 2 ∧ 2 ≤ j.val) →
        (A : Matrix (Fin 4) (Fin 4) K) i j = κ * (1 : Matrix (Fin 4) (Fin 4) K) i j := by
  set Am : Matrix (Fin 4) (Fin 4) K := (A : Matrix (Fin 4) (Fin 4) K) with hAm
  obtain ⟨η, hη, hη0⟩ := h.exists_mem_traceZero_ne_zero
  have hηb : h.bar η = -η := eq_neg_of_add_eq_zero_right (h.mem_traceZero.mp hη)
  have hση : σ η ≠ 0 := fun e => hη0 (σ.injective (by rw [e, map_zero]))
  obtain ⟨κ₀, hκ₀, hrow2⟩ := nrA_diag h Am σ hηb hη0 hση 0 2 ⟨by simp, by simp⟩
    (gramForm_nrA_e0 h) hΦ
  obtain ⟨κ₁, hκ₁, hrow3⟩ := nrA_diag h Am σ hηb hη0 hση 1 3 ⟨by simp, by simp⟩
    (gramForm_nrA_e1 h) hΦ
  have hAinj : ∀ v : Fin 4 → K, Am *ᵥ v = 0 → v = 0 := by
    intro v hv
    have hAi : (↑(A⁻¹) : Matrix (Fin 4) (Fin 4) K) * Am = 1 := by
      rw [hAm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc v = (1 : Matrix (Fin 4) (Fin 4) K) *ᵥ v := (one_mulVec v).symm
      _ = (↑(A⁻¹) * Am) *ᵥ v := by rw [hAi]
      _ = 0 := by rw [← mulVec_mulVec, hv, mulVec_zero]
  have hκ₀ne : κ₀ ≠ 0 := by
    intro e
    rw [e, zero_smul, semilin_single] at hκ₀
    have h3 := congrFun (hAinj _ hκ₀) 0
    simp at h3
  have hE : ∀ a : K, ∀ x : Fin 4 → K,
      σ (x 2) • σ a • semilin Am σ (Pi.single 1 1) -
          σ (h.bar a * x 3) • semilin Am σ (Pi.single 0 1) =
        (semilin Am σ x 2) • a • (Pi.single 1 1 : Fin 4 → K) -
          (h.bar a * semilin Am σ x 3) • (Pi.single 0 1 : Fin 4 → K) := by
    intro a x
    have hy : (a • (Pi.single 1 1 : Fin 4 → K)) ∈
        (nrL K).orthogonalBilin (gramForm h (nrGramA K)) :=
      (mem_orthogonalBilin_nrL h).mpr ⟨by simp, by simp⟩
    have hadm : (0 : K) + h.bar 0 = -gramForm h (nrGramA K) (a • (Pi.single 1 1 : Fin 4 → K))
        (a • (Pi.single 1 1 : Fin 4 → K)) := by
      rw [gramForm_nrA_smul_e1]
      simp
    have h1 := hΦ (Pi.single 0 1) (a • Pi.single 1 1) 0 ⟨by simp, by simp⟩ hy hadm x
    rw [eichlerMatrix_mulVec, eichlerMatrix_mulVec, gramForm_nrA_e0, gramForm_nrA_e0,
      gramForm_nrA_smul_e1, gramForm_nrA_smul_e1] at h1
    simp only [zero_mul, zero_smul, add_zero] at h1
    rw [semilin_sub, semilin_add, semilin_smul, semilin_smul, semilin_smul] at h1
    rw [add_sub_assoc, add_sub_assoc] at h1
    exact add_left_cancel h1
  have hE1 : ∀ a : K, σ a * κ₁ = σ η / η * κ₀ * a := by
    intro a
    have h1 := congrFun (hE a (Pi.single 2 1)) 1
    simp [hκ₀, hκ₁, hrow2, hrow3] at h1
    exact h1
  have hE0 : ∀ a : K, σ (h.bar a) * κ₀ = h.bar a * (σ η / η * κ₁) := by
    intro a
    have h1 := congrFun (hE a (Pi.single 3 1)) 0
    simp [hκ₀, hκ₁, hrow2, hrow3] at h1
    exact h1
  have hs0 : σ η / η ≠ 0 := div_ne_zero hση hη0
  have hκ₁s : κ₁ = σ η / η * κ₀ := by
    have := hE1 1
    simpa using this
  have hκ₁ne : κ₁ ≠ 0 := by
    rw [hκ₁s]
    exact mul_ne_zero hs0 hκ₀ne
  have hσ : ∀ t, σ t = t := by
    intro t
    have h1 := hE1 t
    rw [hκ₁s] at h1
    have h2 : (σ η / η * κ₀) * (σ t - t) = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (mul_ne_zero hs0 hκ₀ne))
  have hs1 : σ η / η = 1 := by rw [hσ η, div_self hη0]
  have hκ₁₀ : κ₁ = κ₀ := by rw [hκ₁s, hs1, one_mul]
  have hΦA : ∀ x : Fin 4 → K, semilin Am σ x = Am *ᵥ x := by
    intro x
    simp only [semilin]
    congr 1
    funext i
    exact hσ _
  have hshape : ∀ i j : Fin 4, ¬ (i.val < 2 ∧ 2 ≤ j.val) →
      Am i j = κ₀ * (1 : Matrix (Fin 4) (Fin 4) K) i j := by
    intro i j hij
    have hcol : Am i j = semilin Am σ (Pi.single j 1) i := by
      rw [semilin_single, mulVec_single_one, col_apply]
    fin_cases j
    · rw [hcol]
      simp only [Fin.zero_eta]
      rw [hκ₀]
      fin_cases i <;> simp
    · rw [hcol]
      simp only [Fin.mk_one]
      rw [hκ₁, hκ₁₀]
      fin_cases i <;> simp
    · fin_cases i
      · exact absurd (by simp) hij
      · exact absurd (by simp) hij
      · rw [hcol]
        simp only [Fin.reduceFinMk, Fin.isValue]
        rw [hrow2, hs1, hσ]
        simp
      · rw [hcol]
        simp only [Fin.reduceFinMk, Fin.isValue]
        rw [hrow3, hs1, hσ, hκ₁₀]
        simp
    · fin_cases i
      · exact absurd (by simp) hij
      · exact absurd (by simp) hij
      · rw [hcol]
        simp only [Fin.reduceFinMk, Fin.isValue]
        rw [hrow2, hs1, hσ]
        simp
      · rw [hcol]
        simp only [Fin.reduceFinMk, Fin.isValue]
        rw [hrow3, hs1, hσ, hκ₁₀]
        simp
  have hH : ∀ x y : Fin 4 → K, gramForm h (nrGramA K) (Am *ᵥ x) (Am *ᵥ y) =
      gramForm h (nrGramA K) x y :=
    (gramForm_isometry_iff h _ _).mpr (mem_primeFormUnitary.mp hA)
  have hn1 : h.bar κ₀ * κ₀ = 1 := by
    have h1 := hH (Pi.single 0 1) (Pi.single 2 1)
    have hA0 : Am *ᵥ (Pi.single 0 1 : Fin 4 → K) = κ₀ • (Pi.single 0 1 : Fin 4 → K) := by
      rw [← hΦA]
      exact hκ₀
    have hA2 : (Am *ᵥ (Pi.single 2 1 : Fin 4 → K)) 2 = κ₀ := by
      rw [mulVec_single_one, col_apply, hshape 2 2 (by simp)]
      simp
    rw [hA0, map_smulₛₗ, LinearMap.smul_apply, gramForm_nrA_e0, gramForm_nrA_e0, hA2,
      smul_eq_mul] at h1
    simpa using h1
  refine ⟨hσ, κ₀, hκ₀ne, ?_, hshape⟩
  rw [UnitaryFieldData.norm, mul_comm]
  exact hn1

theorem nrNilA_mulVec (η : K) (x : Fin 4 → K) :
    nrNilA η *ᵥ x =
      η • (x 2 • (Pi.single 0 1 : Fin 4 → K) + x 3 • (Pi.single 1 1 : Fin 4 → K)) := by
  funext i
  fin_cases i <;> simp [nrNilA, mulVec, dotProduct, Fin.sum_univ_four]

theorem nrNilA_mulVec_mem (η : K) (x : Fin 4 → K) : nrNilA η *ᵥ x ∈ nrL K := by
  rw [mem_nrL]
  rw [nrNilA_mulVec]
  simp

theorem nrNilA_mulVec_of_mem (η : K) {w : Fin 4 → K} (hw : w ∈ nrL K) : nrNilA η *ᵥ w = 0 := by
  rw [nrNilA_mulVec, hw.1, hw.2]
  simp

theorem nrL_fix_comm {η : K} {r : gramSU h (nrGramA K)} (hr : r ∈ isotropicRadical h (nrGramA K)
    (nrL K)) :
    ((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * nrNilA η =
      nrNilA η * ((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  apply KCUnitaryTrv.matrix_eq_of_mulVec_eq
  intro x
  obtain ⟨hr1, hr2, hr3⟩ := mem_isotropicRadical.mp hr
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  have h1 : ((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ (nrNilA η *ᵥ x) =
      nrNilA η *ᵥ x := hr1 _ (nrNilA_mulVec_mem η x)
  have h2 : ((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x - x ∈ nrL K := by
    have := hr3 x
    rwa [mem_orthogonalBilin_nrL h, ← mem_nrL] at this
  rw [h1]
  calc nrNilA η *ᵥ x =
        nrNilA η *ᵥ (x + (((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x - x)) := by
        rw [mulVec_add, nrNilA_mulVec_of_mem η h2, add_zero]
    _ = nrNilA η *ᵥ (((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ x) := by
        congr 1
        abel

theorem exists_nrNilA_mulVec_eq {η : K} (hη0 : η ≠ 0) {w : Fin 4 → K} (hw : w ∈ nrL K) :
    ∃ x : Fin 4 → K, nrNilA η *ᵥ x = w := by
  refine ⟨η⁻¹ • (w 0 • (Pi.single 2 1 : Fin 4 → K) + w 1 • (Pi.single 3 1 : Fin 4 → K)), ?_⟩
  rw [nrNilA_mulVec]
  funext i
  fin_cases i <;> simp [hw.1, hw.2, hη0]

theorem nrAR_conj_mem {η : K} (hη0 : η ≠ 0) {g : gramSU h (nrGramA K)}
    (hg : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * nrNilA η =
      nrNilA η * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    {r : gramSU h (nrGramA K)} (hr : r ∈ isotropicRadical h (nrGramA K) (nrL K)) :
    g * r * g⁻¹ ∈ isotropicRadical h (nrGramA K) (nrL K) := by
  set gm : Matrix (Fin 4) (Fin 4) K := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hgm
  set gi : Matrix (Fin 4) (Fin 4) K :=
    (((g⁻¹ : gramSU h (nrGramA K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hgi
  have hgi' : ((g⁻¹ : gramSU h (nrGramA K)) : GL (Fin 4) K) = (g : GL (Fin 4) K)⁻¹ := rfl
  have hgg : gm * gi = 1 := by rw [hgm, hgi, hgi', Units.mul_inv]
  have hgg' : gi * gm = 1 := by rw [hgm, hgi, hgi', Units.inv_mul]
  have hgi_comm : gi * nrNilA η = nrNilA η * gi := by
    have h1 := congrArg (fun X => gi * X * gi) hg
    have e1 : gi * (gm * nrNilA η) * gi = nrNilA η * gi := by
      rw [← Matrix.mul_assoc gi gm, hgg', Matrix.one_mul]
    have e2 : gi * (nrNilA η * gm) * gi = gi * nrNilA η := by
      rw [Matrix.mul_assoc gi (nrNilA η * gm) gi, Matrix.mul_assoc (nrNilA η) gm gi, hgg,
        Matrix.mul_one]
    rw [e1, e2] at h1
    exact h1.symm
  have hW : ∀ (M : Matrix (Fin 4) (Fin 4) K), M * nrNilA η = nrNilA η * M →
      ∀ w ∈ nrL K, M *ᵥ w ∈ nrL K := by
    intro M hM w hw
    obtain ⟨x, rfl⟩ := exists_nrNilA_mulVec_eq hη0 hw
    rw [mulVec_mulVec, hM, ← mulVec_mulVec]
    exact nrNilA_mulVec_mem η _
  exact KCUnitaryDefining.conj_mem_isotropicRadical h (hW gm hg) (hW gi hgi_comm) hr

theorem semilin_mulVec_of_exact {n : ℕ} (A : GL (Fin n) K) (σ : K ≃+* K)
    (E : Matrix (Fin n) (Fin n) K)
    (hE : (A : Matrix (Fin n) (Fin n) K) * E.map σ * (↑(A⁻¹) : Matrix (Fin n) (Fin n) K) = E)
    (x : Fin n → K) :
    semilin (A : Matrix (Fin n) (Fin n) K) σ (E *ᵥ x) =
      E *ᵥ semilin (A : Matrix (Fin n) (Fin n) K) σ x := by
  apply semilin_mulVec _ x
  have hAi : (↑(A⁻¹) : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc (A : Matrix (Fin n) (Fin n) K) * E.map σ =
      (A : Matrix (Fin n) (Fin n) K) * E.map σ *
        (↑(A⁻¹) * (A : Matrix (Fin n) (Fin n) K)) := by rw [hAi, Matrix.mul_one]
    _ = ((A : Matrix (Fin n) (Fin n) K) * E.map σ * ↑(A⁻¹)) * (A : Matrix (Fin n) (Fin n) K) :=
        (Matrix.mul_assoc _ _ _).symm
    _ = E * (A : Matrix (Fin n) (Fin n) K) := by rw [hE]

theorem nrAR_pointwise (A : primeFormUnitary h (nrGramA K)) (σ : K ≃+* K)
    (hexact : ∀ r ∈ isotropicRadical h (nrGramA K) (nrL K),
      (A : GL (Fin 4) K) * glAut σ (r : GL (Fin 4) K) * (A : GL (Fin 4) K)⁻¹ = r) :
    ∃ r' ∈ isotropicRadical h (nrGramA K) (nrL K),
      primeFormConjHom h (nrGramA K) A * primeFormFieldHom h (isPrimeFormGram_nrA (K := K)) σ =
        MulAut.conj (r' : primeFormP h (nrGramA K)) := by
  have hΦ : ∀ (w y : Fin 4 → K) (c : K), w ∈ nrL K →
      y ∈ (nrL K).orthogonalBilin (gramForm h (nrGramA K)) →
      c + h.bar c = -gramForm h (nrGramA K) y y → ∀ x : Fin 4 → K,
      semilin ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) σ
          (eichlerMatrix h (nrGramA K) w y c *ᵥ x) =
        eichlerMatrix h (nrGramA K) w y c *ᵥ
          semilin ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) σ x := by
    intro w y c hw hy hc x
    have h1 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K))
      (hexact _ (eichler_mem_radical (gramForm_nrA_symm h) (nrL_iso h) hw hy hc))
    simp only [Units.val_mul, coe_glAut] at h1
    exact semilin_mulVec_of_exact (A : GL (Fin 4) K) σ _ h1 x
  obtain ⟨hσ, κ, hκ0, hκn, hshape⟩ := nrA_pointwise h (A : GL (Fin 4) K) A.2 σ hΦ
  set Am : Matrix (Fin 4) (Fin 4) K := ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hAm
  have hM0 : ∀ i j : Fin 4, ¬ (i.val < 2 ∧ 2 ≤ j.val) →
      (Am - κ • (1 : Matrix (Fin 4) (Fin 4) K)) i j = 0 := by
    intro i j hij
    rw [Matrix.sub_apply, hshape i j hij, Matrix.smul_apply, smul_eq_mul, sub_self]
  have hnil : IsNilpotent (Am - κ • (1 : Matrix (Fin 4) (Fin 4) K)) := by
    refine ⟨2, ?_⟩
    rw [pow_two]
    ext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : i.val < 2 ∧ 2 ≤ k.val
    · rw [hM0 k j (by omega), mul_zero]
    · rw [hM0 i k hik, zero_mul]
  obtain ⟨r, hAr, hrm⟩ := exists_gramSU_of_unipotent (C := nrGLA K) h A.2 hκ0 hκn hnil
  refine ⟨r, ?_,
    KCUnitaryDefining.primeFormConjHom_mul_fieldHom_eq_conj h isPrimeFormGram_nrA hAr hσ⟩
  set rm : Matrix (Fin 4) (Fin 4) K := ((r : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hrmdef
  have hrsh : ∀ i j : Fin 4, ¬ (i.val < 2 ∧ 2 ≤ j.val) →
      rm i j = (1 : Matrix (Fin 4) (Fin 4) K) i j := by
    intro i j hij
    rw [hrm, Matrix.smul_apply, smul_eq_mul, ← hAm, hshape i j hij, ← mul_assoc,
      inv_mul_cancel₀ hκ0, one_mul]
  have hfixL : ∀ w ∈ nrL K, rm *ᵥ w = w := by
    intro w hw
    funext i
    simp only [mulVec, dotProduct, Fin.sum_univ_four, hw.1, hw.2, mul_zero, add_zero]
    rw [hrsh i 0 (by simp), hrsh i 1 (by simp)]
    fin_cases i <;> simp [hw.1, hw.2, Matrix.one_apply]
  have hrow : ∀ v : Fin 4 → K, (rm *ᵥ v) 2 = v 2 ∧ (rm *ᵥ v) 3 = v 3 := by
    intro v
    constructor
    · simp only [mulVec, dotProduct, Fin.sum_univ_four]
      rw [hrsh 2 0 (by simp), hrsh 2 1 (by simp), hrsh 2 2 (by simp), hrsh 2 3 (by simp)]
      simp
    · simp only [mulVec, dotProduct, Fin.sum_univ_four]
      rw [hrsh 3 0 (by simp), hrsh 3 1 (by simp), hrsh 3 2 (by simp), hrsh 3 3 (by simp)]
      simp
  refine mem_isotropicRadical.mpr ⟨hfixL, fun v hv => ?_, fun v => ?_⟩
  · have hvL : v ∈ nrL K := (mem_orthogonalBilin_nrL h).mp hv
    rw [hfixL v hvL, sub_self]
    exact zero_mem _
  · rw [mem_orthogonalBilin_nrL h]
    exact ⟨sub_eq_zero.mpr (hrow v).1, sub_eq_zero.mpr (hrow v).2⟩

theorem nrA_normalPrimeComplementsTrivial (hp3 : 3 < p) {η : K} (hη : h.bar η = -η)
    (hη0 : η ≠ 0) :
    NormalPrimeComplementsTrivial p
      (MulAut.conj (nrEltA h hp3 hη : primeFormP h (nrGramA K))) := by
  have hn : 3 ≤ 4 := by norm_num
  have hnp : 4 ≤ p := by omega
  refine KCUnitaryDefining.normalPrimeComplementsTrivial_of_radical_data (C := nrGLA K) h hp3 hn
    isPrimeFormGram_nrA (nrEltA h hp3 hη) (unitaryExp_pow_eq_one h hp3 hn hnp isPrimeFormGram_nrA
      (nrNilA_pow_four η) (nrNilA_skew h hη)) (nrNilA η)
    (fun g hg => (unitaryExp_comm_iff h hp3 hn hnp isPrimeFormGram_nrA (nrNilA_pow_four η)
      (nrNilA_skew h hη) g).mp hg) (isotropicRadical h (nrGramA K) (nrL K))
    (fun r hr => (unitaryExp_comm_iff h hp3 hn hnp isPrimeFormGram_nrA (nrNilA_pow_four η)
      (nrNilA_skew h hη) r).mpr (nrL_fix_comm h hr))
    (fun r hr => KCUnitaryDefining.pow_eq_one_of_mem_isotropicRadical h hp3.le (by norm_num) hr)
    (fun g hg r hr => nrAR_conj_mem h hη0 hg hr)
    (fun A σ hex => nrAR_pointwise h A σ hex)

end KCUnitaryNr

end CFSG.RankThree.PartOne

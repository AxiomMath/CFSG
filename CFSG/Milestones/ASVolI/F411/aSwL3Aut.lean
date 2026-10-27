module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public noncomputable section

namespace CFSG.ASVolI

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def burnsideF411a_w0 (K : Type) [Field K] : GL (Fin 3) K where
  val := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  inv := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

variable {K : Type} [Field K]

theorem burnsideF411a_w0_mulVec (v : Fin 3 → K) :
    ((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = ![v 2, v 1, v 0] := by
  funext i
  fin_cases i <;> simp [burnsideF411a_w0, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem burnsideF411a_w0_mulVec_mulVec (v : Fin 3 → K) :
    ((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = v := by
  rw [burnsideF411a_w0_mulVec, burnsideF411a_w0_mulVec]
  funext i
  fin_cases i <;> rfl

theorem burnsideF411a_w0_inv : (burnsideF411a_w0 K)⁻¹ = burnsideF411a_w0 K :=
  Units.ext rfl

theorem burnsideF411a_w0_mul_self : burnsideF411a_w0 K * burnsideF411a_w0 K = 1 := by
  conv_lhs => rw [← burnsideF411a_w0_inv (K := K)]
  exact inv_mul_cancel _

theorem burnsideF411a_inverseTranspose_w0 :
    GeneralLinearGroup.inverseTranspose (burnsideF411a_w0 K) = burnsideF411a_w0 K := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose, burnsideF411a_w0_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem burnsideF411a_map_w0 (σ : K ≃+* K) :
    GeneralLinearGroup.map (σ : K →+* K) (burnsideF411a_w0 K) = burnsideF411a_w0 K := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideF411a_w0]

theorem burnsideF411a_coordImage_flagSpace (σ : K ≃+* K) (d : ℕ) :
    coordImage σ (flagSpace 3 K d) = flagSpace 3 K d := by
  ext v
  rw [mem_coordImage, mem_flagSpace, mem_flagSpace]
  exact forall₂_congr fun j _ => by simp

theorem burnsideF411a_single_zero_mem : (Pi.single 0 1 : Fin 3 → K) ∈ flagSpace 3 K 1 := by
  rw [mem_flagSpace]
  intro j hj
  have hj0 : j ≠ 0 := fun h => by subst h; simp at hj
  simp [Pi.single_apply, hj0]

theorem burnsideF411a_single_one_mem : (Pi.single 1 1 : Fin 3 → K) ∈ flagSpace 3 K 2 := by
  rw [mem_flagSpace]
  intro j hj
  have hj1 : j ≠ 1 := fun h => by subst h; simp at hj
  simp [Pi.single_apply, hj1]

theorem burnsideF411a_flagSpace_one_le : flagSpace 3 K 1 ≤ flagSpace 3 K 2 := fun v hv =>
  mem_flagSpace.2 fun j hj => mem_flagSpace.1 hv j (by omega)

theorem burnsideF411a_w0_dotOrth_one :
    (dotOrth (flagSpace 3 K 1)).map
        (mulVecLin ((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      flagSpace 3 K 2 := by
  ext v
  rw [Submodule.mem_map, mem_flagSpace]
  constructor
  · rintro ⟨u, hu, rfl⟩ j hj
    rw [mem_dotOrth] at hu
    have h0 := hu _ burnsideF411a_single_zero_mem
    rw [dotProduct_single, mul_one] at h0
    have hj2 : j = 2 := Fin.ext (by have := j.2; omega)
    subst hj2
    rw [mulVecLin_apply, burnsideF411a_w0_mulVec]
    simpa using h0
  · intro hv
    refine ⟨((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v, ?_, ?_⟩
    · rw [mem_dotOrth]
      intro w hw
      rw [mem_flagSpace] at hw
      have hw1 := hw 1 (by decide)
      have hw2 := hw 2 (by decide)
      have hv2 := hv 2 (by decide)
      rw [burnsideF411a_w0_mulVec]
      simp [dotProduct, Fin.sum_univ_three, hw1, hw2, hv2]
    · rw [mulVecLin_apply, burnsideF411a_w0_mulVec_mulVec]

theorem burnsideF411a_w0_dotOrth_two :
    (dotOrth (flagSpace 3 K 2)).map
        (mulVecLin ((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      flagSpace 3 K 1 := by
  ext v
  rw [Submodule.mem_map, mem_flagSpace]
  constructor
  · rintro ⟨u, hu, rfl⟩ j hj
    rw [mem_dotOrth] at hu
    have h0 := hu _ (burnsideF411a_flagSpace_one_le burnsideF411a_single_zero_mem)
    have h1 := hu _ burnsideF411a_single_one_mem
    rw [dotProduct_single, mul_one] at h0 h1
    rw [mulVecLin_apply, burnsideF411a_w0_mulVec]
    have hj' : j = 1 ∨ j = 2 := by
      rcases j with ⟨j, hj3⟩
      simp only [Fin.ext_iff]
      simp only at hj
      omega
    rcases hj' with rfl | rfl
    · simpa using h1
    · simpa using h0
  · intro hv
    refine ⟨((burnsideF411a_w0 K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v, ?_, ?_⟩
    · rw [mem_dotOrth]
      intro w hw
      rw [mem_flagSpace] at hw
      have hw2 := hw 2 (by decide)
      have hv1 := hv 1 (by decide)
      have hv2 := hv 2 (by decide)
      rw [burnsideF411a_w0_mulVec]
      simp [dotProduct, Fin.sum_univ_three, hw2, hv1, hv2]
    · rw [mulVecLin_apply, burnsideF411a_w0_mulVec_mulVec]

variable (K) in
@[expose] noncomputable def burnsideF411a_L3zeta (τ : K ≃+* K) : MulAut (projectiveSL 3 K) :=
  conjAut 3 K (burnsideF411a_w0 K) * dualAut 3 K * fieldAut 3 K τ

theorem burnsideF411a_L3zeta_coe (τ : K ≃+* K) :
    (burnsideF411a_L3zeta K τ : projectiveSL 3 K →* projectiveSL 3 K) =
      (conjAut 3 K (burnsideF411a_w0 K) : projectiveSL 3 K →* projectiveSL 3 K).comp
        ((dualAut 3 K : projectiveSL 3 K →* projectiveSL 3 K).comp
          (fieldAut 3 K τ : projectiveSL 3 K →* projectiveSL 3 K)) :=
  MonoidHom.ext fun _ => rfl

theorem burnsideF411a_L3zeta_map_flag_one (τ : K ≃+* K) :
    (projStabilizer (flagSpace 3 K 1)).map
        (burnsideF411a_L3zeta K τ : projectiveSL 3 K →* projectiveSL 3 K) =
      projStabilizer (flagSpace 3 K 2) := by
  obtain ⟨-, -, -, -, -, -, hc, hf, hd, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  rw [burnsideF411a_L3zeta_coe, ← Subgroup.map_map, ← Subgroup.map_map, hf,
    burnsideF411a_coordImage_flagSpace, hd, hc, burnsideF411a_w0_dotOrth_one]

theorem burnsideF411a_L3zeta_map_flag_two (τ : K ≃+* K) :
    (projStabilizer (flagSpace 3 K 2)).map
        (burnsideF411a_L3zeta K τ : projectiveSL 3 K →* projectiveSL 3 K) =
      projStabilizer (flagSpace 3 K 1) := by
  obtain ⟨-, -, -, -, -, -, hc, hf, hd, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  rw [burnsideF411a_L3zeta_coe, ← Subgroup.map_map, ← Subgroup.map_map, hf,
    burnsideF411a_coordImage_flagSpace, hd, hc, burnsideF411a_w0_dotOrth_two]

theorem burnsideF411a_dualAut_inv : (dualAut 3 K)⁻¹ = dualAut 3 K :=
  inv_eq_of_mul_eq_one_right (standard_automorphism_transport (K := K) (n := 3)).2.2.2.1

theorem burnsideF411a_L3zeta_inv (τ : K ≃+* K) :
    (burnsideF411a_L3zeta K τ)⁻¹ =
      (fieldAut 3 K τ)⁻¹ * dualAut 3 K * (conjAut 3 K (burnsideF411a_w0 K))⁻¹ := by
  rw [burnsideF411a_L3zeta, _root_.mul_inv_rev, _root_.mul_inv_rev, burnsideF411a_dualAut_inv,
    mul_assoc]

theorem burnsideF411a_L3zeta_conj_conjAut (τ : K ≃+* K) (A : GL (Fin 3) K) :
    burnsideF411a_L3zeta K τ * conjAut 3 K A * (burnsideF411a_L3zeta K τ)⁻¹ =
      conjAut 3 K (burnsideF411a_w0 K *
        GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.map (τ : K →+* K) A) *
          (burnsideF411a_w0 K)⁻¹) := by
  obtain ⟨-, -, h3, -, h5, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  rw [burnsideF411a_L3zeta_inv, map_mul, map_mul, map_inv, ← h5, ← h3]
  simp only [burnsideF411a_L3zeta, mul_assoc]

theorem burnsideF411a_L3zeta_conj_fieldAut (τ σ : K ≃+* K) (hτσ : τ * σ = σ * τ) :
    burnsideF411a_L3zeta K τ * fieldAut 3 K σ * (burnsideF411a_L3zeta K τ)⁻¹ =
      fieldAut 3 K σ := by
  obtain ⟨-, -, h3, -, -, h6, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  have hFσ : fieldAut 3 K τ * fieldAut 3 K σ * (fieldAut 3 K τ)⁻¹ = fieldAut 3 K σ := by
    rw [← map_mul, ← map_inv, ← map_mul, hτσ, mul_inv_cancel_right]
  have hcw : conjAut 3 K (burnsideF411a_w0 K) * fieldAut 3 K σ *
      (conjAut 3 K (burnsideF411a_w0 K))⁻¹ = fieldAut 3 K σ := by
    have h := h3 σ (burnsideF411a_w0 K)
    rw [burnsideF411a_map_w0] at h
    have hfc : fieldAut 3 K σ * conjAut 3 K (burnsideF411a_w0 K) =
        conjAut 3 K (burnsideF411a_w0 K) * fieldAut 3 K σ := by
      calc fieldAut 3 K σ * conjAut 3 K (burnsideF411a_w0 K)
          = fieldAut 3 K σ * conjAut 3 K (burnsideF411a_w0 K) * (fieldAut 3 K σ)⁻¹ *
              fieldAut 3 K σ := by group
        _ = conjAut 3 K (burnsideF411a_w0 K) * fieldAut 3 K σ := by rw [h]
    rw [← hfc, mul_inv_cancel_right]
  calc burnsideF411a_L3zeta K τ * fieldAut 3 K σ * (burnsideF411a_L3zeta K τ)⁻¹
      = conjAut 3 K (burnsideF411a_w0 K) * (dualAut 3 K * (fieldAut 3 K τ * fieldAut 3 K σ *
          (fieldAut 3 K τ)⁻¹) * dualAut 3 K) * (conjAut 3 K (burnsideF411a_w0 K))⁻¹ := by
        rw [burnsideF411a_L3zeta_inv, burnsideF411a_L3zeta]
        group
    _ = conjAut 3 K (burnsideF411a_w0 K) * (dualAut 3 K * fieldAut 3 K σ * dualAut 3 K) *
          (conjAut 3 K (burnsideF411a_w0 K))⁻¹ := by rw [hFσ]
    _ = fieldAut 3 K σ := by rw [h6, hcw]

theorem burnsideF411a_L3zeta_conj_dualAut (τ : K ≃+* K) :
    burnsideF411a_L3zeta K τ * dualAut 3 K * (burnsideF411a_L3zeta K τ)⁻¹ = dualAut 3 K := by
  obtain ⟨-, -, -, h4, h5, h6, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  have hfd : fieldAut 3 K τ * dualAut 3 K * (fieldAut 3 K τ)⁻¹ = dualAut 3 K := by
    have h := h6 τ
    calc fieldAut 3 K τ * dualAut 3 K * (fieldAut 3 K τ)⁻¹
        = (dualAut 3 K * fieldAut 3 K τ * dualAut 3 K) * dualAut 3 K *
            (fieldAut 3 K τ)⁻¹ := by rw [h]
      _ = dualAut 3 K * fieldAut 3 K τ * (dualAut 3 K * dualAut 3 K) *
            (fieldAut 3 K τ)⁻¹ := by group
      _ = dualAut 3 K := by rw [h4, mul_one, mul_inv_cancel_right]
  have hcd : conjAut 3 K (burnsideF411a_w0 K) * dualAut 3 K *
      (conjAut 3 K (burnsideF411a_w0 K))⁻¹ = dualAut 3 K := by
    have h := h5 (burnsideF411a_w0 K)⁻¹
    rw [burnsideF411a_w0_inv, burnsideF411a_inverseTranspose_w0] at h
    have e1 : (conjAut 3 K (burnsideF411a_w0 K))⁻¹ = conjAut 3 K (burnsideF411a_w0 K) := by
      rw [← map_inv, burnsideF411a_w0_inv]
    rw [e1]
    calc conjAut 3 K (burnsideF411a_w0 K) * dualAut 3 K * conjAut 3 K (burnsideF411a_w0 K)
        = (dualAut 3 K * conjAut 3 K (burnsideF411a_w0 K) * dualAut 3 K) * dualAut 3 K *
            conjAut 3 K (burnsideF411a_w0 K) := by rw [h]
      _ = dualAut 3 K * conjAut 3 K (burnsideF411a_w0 K) * (dualAut 3 K * dualAut 3 K) *
            conjAut 3 K (burnsideF411a_w0 K) := by group
      _ = dualAut 3 K * (conjAut 3 K (burnsideF411a_w0 K) *
            conjAut 3 K (burnsideF411a_w0 K)) := by rw [h4, mul_one, mul_assoc]
      _ = dualAut 3 K := by
          rw [← map_mul, burnsideF411a_w0_mul_self, map_one, mul_one]
  calc burnsideF411a_L3zeta K τ * dualAut 3 K * (burnsideF411a_L3zeta K τ)⁻¹
      = conjAut 3 K (burnsideF411a_w0 K) * (dualAut 3 K * (fieldAut 3 K τ * dualAut 3 K *
          (fieldAut 3 K τ)⁻¹) * dualAut 3 K) * (conjAut 3 K (burnsideF411a_w0 K))⁻¹ := by
        rw [burnsideF411a_L3zeta_inv, burnsideF411a_L3zeta]
        group
    _ = conjAut 3 K (burnsideF411a_w0 K) * (dualAut 3 K * dualAut 3 K * dualAut 3 K) *
          (conjAut 3 K (burnsideF411a_w0 K))⁻¹ := by rw [hfd]
    _ = dualAut 3 K := by rw [h4, one_mul, hcd]

theorem burnsideF411a_det_map (τ : K ≃+* K) (A : GL (Fin 3) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.map (τ : K →+* K) A) =
      Units.map (τ : K →* K) (GeneralLinearGroup.det A) := by
  exact GeneralLinearGroup.map_det (τ : K →+* K) A

theorem burnsideF411a_det_inverseTranspose (B : GL (Fin 3) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.inverseTranspose B) =
      (GeneralLinearGroup.det B)⁻¹ := by
  rw [← map_inv]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_inverseTranspose, det_transpose,
    GeneralLinearGroup.val_det_apply]

theorem burnsideF411a_det_L3zeta (τ : K ≃+* K) (A : GL (Fin 3) K) :
    GeneralLinearGroup.det (burnsideF411a_w0 K *
        GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.map (τ : K →+* K) A) *
          (burnsideF411a_w0 K)⁻¹) =
      (Units.map (τ : K →* K) (GeneralLinearGroup.det A))⁻¹ := by
  rw [map_mul, map_mul, map_inv, burnsideF411a_det_inverseTranspose, burnsideF411a_det_map,
    mul_comm (GeneralLinearGroup.det (burnsideF411a_w0 K)), mul_assoc, mul_inv_cancel, mul_one]

theorem burnsideF411a_frob_comm [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (σ : K ≃+* K) :
    frobeniusEquiv K p * σ = σ * frobeniusEquiv K p := by
  ext c
  simp [frobeniusEquiv_apply, frobenius_def, map_pow]

theorem burnsideF411a_L3_cube [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp : p % 3 ≠ 1)
    (u : Kˣ) : ∃ μ : Kˣ, (Units.map (frobeniusEquiv K p : K →* K) u)⁻¹ * u⁻¹ = μ ^ 3 := by
  have hFr : Units.map (frobeniusEquiv K p : K →* K) u = u ^ p :=
    Units.ext (by simp [frobeniusEquiv_apply, frobenius_def])
  rw [hFr]
  rcases (show p % 3 = 0 ∨ p % 3 = 2 by omega) with h0 | h2
  · have h3p : 3 = p :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).1 (Nat.dvd_of_mod_eq_zero h0)
    subst h3p
    refine ⟨Units.map ((frobeniusEquiv K 3).symm : K →* K) ((u ^ 3)⁻¹ * u⁻¹), ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.coe_map]
    exact (frobeniusEquiv_symm_pow_p K 3 _).symm
  · obtain ⟨m, hm⟩ : 3 ∣ p + 1 := by omega
    refine ⟨(u ^ m)⁻¹, ?_⟩
    calc (u ^ p)⁻¹ * u⁻¹ = (u ^ (p + 1))⁻¹ := by rw [pow_succ, mul_inv]
      _ = ((u ^ m)⁻¹) ^ 3 := by rw [hm, mul_comm 3 m, pow_mul, inv_pow]

theorem burnsideF411a_L3zeta_comm [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hp : p % 3 ≠ 1) (α : MulAut (projectiveSL 3 K)) :
    ∃ g : projectiveSL 3 K, burnsideF411a_L3zeta K (frobeniusEquiv K p) * α *
      (burnsideF411a_L3zeta K (frobeniusEquiv K p))⁻¹ = MulAut.conj g * α := by
  obtain ⟨A, σ, ε, -, rfl⟩ := (automorphism_generation (K := K) (n := 3) (by norm_num)).2 α
  have hc := burnsideF411a_L3zeta_conj_conjAut (frobeniusEquiv K p) A
  have hf := burnsideF411a_L3zeta_conj_fieldAut (frobeniusEquiv K p) σ (burnsideF411a_frob_comm σ)
  have hd := burnsideF411a_L3zeta_conj_dualAut (K := K) (frobeniusEquiv K p)
  obtain ⟨μ, hμ⟩ := burnsideF411a_L3_cube hp (GeneralLinearGroup.det A)
  have hdet : GeneralLinearGroup.det ((burnsideF411a_w0 K *
      GeneralLinearGroup.inverseTranspose
        (GeneralLinearGroup.map ((frobeniusEquiv K p : K ≃+* K) : K →+* K) A) *
      (burnsideF411a_w0 K)⁻¹) * A⁻¹) = μ ^ 3 := by
    rw [map_mul, map_inv, burnsideF411a_det_L3zeta]
    exact hμ
  obtain ⟨g, hg⟩ := conjAut_mem_range_conj_of_det_eq_pow hdet
  have hg' : MulAut.conj g = conjAut 3 K (burnsideF411a_w0 K *
      GeneralLinearGroup.inverseTranspose
        (GeneralLinearGroup.map ((frobeniusEquiv K p : K ≃+* K) : K →+* K) A) *
      (burnsideF411a_w0 K)⁻¹) * (conjAut 3 K A)⁻¹ := by
    rw [hg, map_mul (conjAut 3 K) _ A⁻¹, map_inv (conjAut 3 K) A]
  refine ⟨g, ?_⟩
  have key : ∀ x : MulAut (projectiveSL 3 K),
      burnsideF411a_L3zeta K (frobeniusEquiv K p) * x *
        (burnsideF411a_L3zeta K (frobeniusEquiv K p))⁻¹ =
      MulAut.conj (burnsideF411a_L3zeta K (frobeniusEquiv K p)) x :=
    fun x => (MulAut.conj_apply _ _).symm
  rw [key, map_mul, map_mul, map_pow, ← key, ← key, ← key, hc, hf, hd, hg']
  group

end CFSG.ASVolI
